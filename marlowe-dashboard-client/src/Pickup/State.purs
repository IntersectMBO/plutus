module Pickup.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe.Dummy (class ManageMarlowe, createWallet, lookupWalletDetails)
import Capability.Toast (class Toast, addToast)
import Control.Monad.Reader (class MonadAsk)
import Data.Either (Either(..))
import Data.Lens (assign, modifying, set, use, view)
import Data.Map (filter, findMin, insert)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.UUID (toString) as UUID
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Foreign.Generic (encodeJSON)
import Halogen (HalogenM, liftEffect, modify_)
import Halogen.Extra (mapSubmodule)
import InputField.State (handleAction, initialState) as InputField
import InputField.Types (Action(..), State) as InputField
import LocalStorage (setItem, removeItem)
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Network.RemoteData (RemoteData(..), fromEither)
import Pickup.Lenses (_card, _pickingUp, _remoteWalletDetails, _walletDropdownOpen, _walletLibrary, _walletIdInput, _walletNicknameInput, _walletNicknameOrId)
import Pickup.Types (Action(..), Card(..), State)
import StaticData (walletLibraryLocalStorageKey, walletDetailsLocalStorageKey)
import Toast.Types (ajaxErrorToast, errorToast)
import WalletData.Lenses (_companionAppId, _walletNickname)
import WalletData.Types (WalletLibrary)
import WalletData.Validation (WalletIdError, WalletNicknameError, parsePlutusAppId, walletNicknameError)
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
  , walletNicknameOrId: mempty
  , walletDropdownOpen: false
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
  Toast m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (OpenCard card) = assign _card $ Just card

handleAction CloseCard = do
  modify_
    $ set _walletNicknameOrId mempty
    <<< set _remoteWalletDetails NotAsked
    <<< set _pickingUp false
    <<< set _card Nothing
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

handleAction (SetWalletNicknameOrId string) = do
  modify_
    $ set _remoteWalletDetails NotAsked
    <<< set _walletNicknameOrId string
  case parsePlutusAppId string of
    Just plutusAppId -> do
      assign _remoteWalletDetails Loading
      ajaxWalletDetails <- lookupWalletDetails plutusAppId
      assign _remoteWalletDetails $ fromEither ajaxWalletDetails
      case ajaxWalletDetails of
        Left ajaxError -> pure unit -- feedback is shown in the view in this case
        Right walletDetails -> do
          -- check whether this wallet ID is already in the walletLibrary ...
          walletLibrary <- use _walletLibrary
          case findMin $ filter (\details -> UUID.toString (unwrap (view _companionAppId details)) == string) walletLibrary of
            Just { key, value } -> do
              -- if so, open the PickupWalletCard
              handleAction $ WalletNicknameInputAction $ InputField.SetValue key
              handleAction $ WalletIdInputAction $ InputField.SetValue string
              handleAction $ OpenCard PickupWalletCard
            Nothing -> do
              -- otherwise open the PickupNewWalletCard
              handleAction $ WalletNicknameInputAction $ InputField.Reset
              handleAction $ WalletNicknameInputAction $ InputField.SetValidator $ walletNicknameError walletLibrary
              handleAction $ WalletIdInputAction $ InputField.SetValue $ UUID.toString (unwrap (view _companionAppId walletDetails))
              handleAction $ OpenCard PickupNewWalletCard
    Nothing -> pure unit

handleAction (SetWalletDropdownOpen walletDropdownOpen) = assign _walletDropdownOpen walletDropdownOpen

handleAction (OpenPickupWalletCardWithDetails walletDetails) = do
  assign _remoteWalletDetails Loading
  ajaxWalletDetails <- lookupWalletDetails $ view _companionAppId walletDetails
  assign _remoteWalletDetails $ fromEither ajaxWalletDetails
  case ajaxWalletDetails of
    Left ajaxError -> handleAction $ OpenCard LocalWalletMissingCard
    Right _ -> do
      handleAction $ SetWalletDropdownOpen false
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
      walletLibrary <- use _walletLibrary
      liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON walletLibrary
      callMainFrameAction $ MainFrame.EnterPlayState walletLibrary walletDetailsWithNickname
    _ -> do
      -- this should never happen (the "Pickup Wallet" button should be disabled unless remoteWalletDetails is Success),
      -- but let's add some sensible behaviour anyway just in case
      handleAction CloseCard
      addToast $ errorToast "Unable to pick up wallet." $ Just "Details for this wallet could not be loaded."

handleAction ClearLocalStorage =
  liftEffect do
    removeItem walletLibraryLocalStorageKey
    removeItem walletDetailsLocalStorageKey
    location_ <- location =<< window
    reload location_

------------------------------------------------------------
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
