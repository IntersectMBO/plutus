module Welcome.State
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
import Toast.Types (ajaxErrorToast, errorToast)
import WalletData.Lenses (_companionAppId, _walletNickname)
import WalletData.Types (WalletLibrary)
import WalletData.Validation (WalletIdError, WalletNicknameError, WalletNicknameOrIdError, parsePlutusAppId, walletNicknameError, walletNicknameOrIdError)
import Web.HTML (window)
import Web.HTML.Location (reload)
import Web.HTML.Window (location)
import Welcome.Lenses (_card, _cardOpen, _enteringDashboardState, _remoteWalletDetails, _walletLibrary, _walletIdInput, _walletNicknameInput, _walletNicknameOrIdInput)
import Welcome.Types (Action(..), Card(..), State)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty

mkInitialState :: WalletLibrary -> State
mkInitialState walletLibrary =
  { walletLibrary
  , card: Nothing
  , cardOpen: false
  , walletNicknameOrIdInput: InputField.initialState
  , walletNicknameInput: InputField.initialState
  , walletIdInput: InputField.initialState
  , remoteWalletDetails: NotAsked
  , enteringDashboardState: false
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
handleAction (OpenCard card) =
  modify_
    $ set _card (Just card)
    <<< set _cardOpen true

handleAction CloseCard = do
  modify_
    $ set _remoteWalletDetails NotAsked
    <<< set _enteringDashboardState false
    <<< set _cardOpen false
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
      handleAction $ OpenCard UseNewWalletCard

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
                -- if so, open the UseWalletCard
                handleAction $ WalletNicknameInputAction $ InputField.SetValue key
                handleAction $ WalletIdInputAction $ InputField.SetValue walletNicknameOrId
                handleAction $ OpenCard UseWalletCard
              Nothing -> do
                -- otherwise open the UseNewWalletCard
                handleAction $ WalletNicknameInputAction $ InputField.Reset
                handleAction $ WalletNicknameInputAction $ InputField.SetValidator $ walletNicknameError walletLibrary
                handleAction $ WalletIdInputAction $ InputField.SetValue $ UUID.toString (unwrap (view _companionAppId walletDetails))
                handleAction $ OpenCard UseNewWalletCard
    InputField.SetValueFromDropdown walletNicknameOrId -> do
      -- in this case we know it's a wallet nickname, and we want to open the use card
      -- for the corresponding wallet
      walletLibrary <- use _walletLibrary
      for_ (lookup walletNicknameOrId walletLibrary) (handleAction <<< OpenUseWalletCardWithDetails)
    _ -> pure unit

handleAction (OpenUseWalletCardWithDetails walletDetails) = do
  assign _remoteWalletDetails Loading
  ajaxWalletDetails <- lookupWalletDetails $ view _companionAppId walletDetails
  assign _remoteWalletDetails $ fromEither ajaxWalletDetails
  case ajaxWalletDetails of
    Left ajaxError -> handleAction $ OpenCard LocalWalletMissingCard
    Right _ -> do
      handleAction $ WalletNicknameOrIdInputAction $ InputField.Reset
      handleAction $ WalletNicknameInputAction $ InputField.SetValue $ view _walletNickname walletDetails
      handleAction $ WalletIdInputAction $ InputField.SetValue $ UUID.toString (unwrap (view _companionAppId walletDetails))
      handleAction $ OpenCard UseWalletCard

handleAction (WalletNicknameInputAction inputFieldAction) = toWalletNicknameInput $ InputField.handleAction inputFieldAction

handleAction (WalletIdInputAction inputFieldAction) = toWalletIdInput $ InputField.handleAction inputFieldAction

handleAction (UseWallet walletNickname) = do
  assign _enteringDashboardState true
  remoteWalletDetails <- use _remoteWalletDetails
  case remoteWalletDetails of
    Success walletDetails -> do
      let
        walletDetailsWithNickname = set _walletNickname walletNickname walletDetails
      modifying _walletLibrary (insert walletNickname walletDetailsWithNickname)
      insertIntoWalletLibrary walletDetailsWithNickname
      walletLibrary <- use _walletLibrary
      callMainFrameAction $ MainFrame.EnterDashboardState walletLibrary walletDetailsWithNickname
    _ -> do
      -- this should never happen (the button to use a wallet should be disabled unless
      -- remoteWalletDetails is Success), but let's add some sensible behaviour anyway just in case
      handleAction CloseCard
      addToast $ errorToast "Unable to use this wallet." $ Just "Details for this wallet could not be loaded."

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
