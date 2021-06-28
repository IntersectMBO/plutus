module Pickup.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe (class ManageMarlowe, createWallet, lookupWalletDetails)
import Capability.MarloweStorage (class ManageMarloweStorage, clearAllLocalStorage, insertIntoWalletLibrary)
import Capability.Toast (class Toast, addToast)
import Control.Monad.Reader (class MonadAsk)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (assign, modifying, set, use, view)
import Data.Map (filter, findMin, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.UUID (toString) as UUID
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, liftEffect, modify_)
import Halogen.Extra (mapSubmodule)
import InputField.State (handleAction, initialState) as InputField
import InputField.Types (Action(..), State) as InputField
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Network.RemoteData (RemoteData(..), fromEither)
import Pickup.Lenses (_card, _pickingUp, _remoteWalletDetails, _walletLibrary, _walletIdInput, _walletNicknameInput, _walletNicknameOrIdInput)
import Pickup.Types (Action(..), Card(..), State)
import Toast.Types (ajaxErrorToast, errorToast)
import WalletData.Lenses (_companionAppId, _walletNickname)
import WalletData.Types (WalletLibrary)
import WalletData.Validation (WalletIdError, WalletNicknameError, WalletNicknameOrIdError, parsePlutusAppId, walletNicknameError, walletNicknameOrIdError)
import Web.HTML (window)
import Web.HTML.Location (reload)
import Web.HTML.Window (location)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty

mkInitialState :: WalletLibrary -> State
mkInitialState walletLibrary =
  { walletLibrary
  , card: Nothing
  , walletNicknameOrIdInput: InputField.initialState
  , walletNicknameInput: InputField.initialState
  , walletIdInput: InputField.initialState
  , remoteWalletDetails: NotAsked
  , pickingUp: false
  }

-- Some actions are handled in `MainFrame.State` because they involve
-- modifications of that state. See Note [State] in MainFrame.State.
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  MainFrameLoop m =>
  ManageMarlowe m =>
  ManageMarloweStorage m =>
  Toast m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (OpenCard card) = assign _card $ Just card

handleAction (CloseCard card) = do
  currentCard <- use _card
  when (currentCard == Just card) do
    modify_
      $ set _remoteWalletDetails NotAsked
      <<< set _pickingUp false
      <<< set _card Nothing
    handleAction $ WalletNicknameOrIdInputAction $ InputField.Reset
    handleAction $ WalletNicknameInputAction $ InputField.Reset
    handleAction $ WalletIdInputAction $ InputField.Reset

handleAction GenerateWallet = do
  walletLibrary <- use _walletLibrary
  assign _remoteWalletDetails Loading
  ajaxWalletDetails <- createWallet
  assign _remoteWalletDetails $ fromEither ajaxWalletDetails
  case ajaxWalletDetails of
    Left ajaxError -> addToast $ ajaxErrorToast "Failed to generate wallet." ajaxError
    Right walletDetails -> do
      handleAction $ WalletNicknameInputAction $ InputField.Reset
      handleAction $ WalletNicknameInputAction $ InputField.SetValidator $ walletNicknameError walletLibrary
      handleAction $ WalletIdInputAction $ InputField.SetValue $ UUID.toString (unwrap (view _companionAppId walletDetails))
      handleAction $ OpenCard PickupNewWalletCard

handleAction (WalletNicknameOrIdInputAction inputFieldAction) = do
  toWalletNicknameOrIdInput $ InputField.handleAction inputFieldAction
  case inputFieldAction of
    InputField.SetValue walletNicknameOrId -> do
      handleAction $ WalletNicknameOrIdInputAction $ InputField.SetValidator $ const Nothing
      assign _remoteWalletDetails NotAsked
      for_ (parsePlutusAppId walletNicknameOrId) \plutusAppId -> do
        assign _remoteWalletDetails Loading
        handleAction $ WalletNicknameOrIdInputAction $ InputField.SetValidator $ walletNicknameOrIdError Loading
        ajaxWalletDetails <- lookupWalletDetails plutusAppId
        assign _remoteWalletDetails $ fromEither ajaxWalletDetails
        handleAction $ WalletNicknameOrIdInputAction $ InputField.SetValidator $ walletNicknameOrIdError $ fromEither ajaxWalletDetails
        case ajaxWalletDetails of
          Left ajaxError -> pure unit -- feedback is shown in the view in this case
          Right walletDetails -> do
            -- check whether this wallet ID is already in the walletLibrary ...
            walletLibrary <- use _walletLibrary
            case findMin $ filter (\details -> UUID.toString (unwrap (view _companionAppId details)) == walletNicknameOrId) walletLibrary of
              Just { key, value } -> do
                -- if so, open the PickupWalletCard
                handleAction $ WalletNicknameInputAction $ InputField.SetValue key
                handleAction $ WalletIdInputAction $ InputField.SetValue walletNicknameOrId
                handleAction $ OpenCard PickupWalletCard
              Nothing -> do
                -- otherwise open the PickupNewWalletCard
                handleAction $ WalletNicknameInputAction $ InputField.Reset
                handleAction $ WalletNicknameInputAction $ InputField.SetValidator $ walletNicknameError walletLibrary
                handleAction $ WalletIdInputAction $ InputField.SetValue $ UUID.toString (unwrap (view _companionAppId walletDetails))
                handleAction $ OpenCard PickupNewWalletCard
    InputField.SetValueFromDropdown walletNicknameOrId -> do
      -- in this case we know it's a wallet nickname, and we want to open the pickup card
      -- for the corresponding wallet
      walletLibrary <- use _walletLibrary
      for_ (lookup walletNicknameOrId walletLibrary) (handleAction <<< OpenPickupWalletCardWithDetails)
    _ -> pure unit

handleAction (OpenPickupWalletCardWithDetails walletDetails) = do
  assign _remoteWalletDetails Loading
  ajaxWalletDetails <- lookupWalletDetails $ view _companionAppId walletDetails
  assign _remoteWalletDetails $ fromEither ajaxWalletDetails
  case ajaxWalletDetails of
    Left ajaxError -> handleAction $ OpenCard LocalWalletMissingCard
    Right _ -> do
      handleAction $ WalletNicknameOrIdInputAction $ InputField.Reset
      handleAction $ WalletNicknameInputAction $ InputField.SetValue $ view _walletNickname walletDetails
      handleAction $ WalletIdInputAction $ InputField.SetValue $ UUID.toString (unwrap (view _companionAppId walletDetails))
      handleAction $ OpenCard PickupWalletCard

handleAction (WalletNicknameInputAction inputFieldAction) = toWalletNicknameInput $ InputField.handleAction inputFieldAction

handleAction (WalletIdInputAction inputFieldAction) = toWalletIdInput $ InputField.handleAction inputFieldAction

handleAction (PickupWallet walletNickname) = do
  assign _pickingUp true
  remoteWalletDetails <- use _remoteWalletDetails
  case remoteWalletDetails of
    Success walletDetails -> do
      let
        walletDetailsWithNickname = set _walletNickname walletNickname walletDetails
      modifying _walletLibrary (insert walletNickname walletDetailsWithNickname)
      insertIntoWalletLibrary walletDetailsWithNickname
      walletLibrary <- use _walletLibrary
      callMainFrameAction $ MainFrame.EnterPlayState walletLibrary walletDetailsWithNickname
    _ -> do
      -- this should never happen (the "Pickup Wallet" button should be disabled unless remoteWalletDetails is Success),
      -- but let's add some sensible behaviour anyway just in case
      handleAction $ CloseCard PickupWalletCard -- either of these cards could be open at
      handleAction $ CloseCard PickupNewWalletCard -- this point, so we close both to be sure
      addToast $ errorToast "Unable to pick up wallet." $ Just "Details for this wallet could not be loaded."

handleAction ClearLocalStorage = do
  clearAllLocalStorage
  liftEffect do
    location_ <- location =<< window
    reload location_

------------------------------------------------------------
toWalletNicknameOrIdInput ::
  forall m msg slots.
  Functor m =>
  HalogenM (InputField.State WalletNicknameOrIdError) (InputField.Action WalletNicknameOrIdError) slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toWalletNicknameOrIdInput = mapSubmodule _walletNicknameOrIdInput WalletNicknameOrIdInputAction

toWalletNicknameInput ::
  forall m msg slots.
  Functor m =>
  HalogenM (InputField.State WalletNicknameError) (InputField.Action WalletNicknameError) slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toWalletNicknameInput = mapSubmodule _walletNicknameInput WalletNicknameInputAction

toWalletIdInput ::
  forall m msg slots.
  Functor m =>
  HalogenM (InputField.State WalletIdError) (InputField.Action WalletIdError) slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toWalletIdInput = mapSubmodule _walletIdInput WalletIdInputAction
