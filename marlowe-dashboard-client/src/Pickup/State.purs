module Pickup.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe (class ManageMarlowe, createWallet, lookupWalletDetails)
import Capability.Toast (class Toast, addToast)
import Control.Monad.Reader (class MonadAsk)
import Data.Either (Either(..))
import Data.Lens (assign, modifying, use, view)
import Data.Map (filter, findMin, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.UUID (toString) as UUID
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Foreign.Generic (encodeJSON)
import Halogen (HalogenM, liftEffect)
import Halogen.Extra (mapSubmodule)
import InputField.State (handleAction, mkInitialState) as InputField
import InputField.Types (Action(..), State) as InputField
import LocalStorage (setItem, removeItem)
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Pickup.Lenses (_card, _walletDetails, _walletLibrary, _walletNicknameOrIdInput)
import Pickup.Types (Action(..), Card(..), State)
import Pickup.Validation (WalletNicknameOrIdError, walletIdError, walletNicknameError)
import StaticData (walletLibraryLocalStorageKey, walletDetailsLocalStorageKey)
import Toast.Types (ajaxErrorToast)
import WalletData.Lenses (_companionAppId, _walletNickname)
import WalletData.State (defaultWalletDetails)
import WalletData.Types (WalletLibrary)
import WalletData.Validation (parsePlutusAppId)
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
  , walletNicknameOrIdInput: InputField.mkInitialState mempty $ walletNicknameError walletLibrary
  , walletDetails: defaultWalletDetails
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

handleAction CloseCard = assign _card Nothing

handleAction GenerateWallet = do
  ajaxWallet <- createWallet
  case ajaxWallet of
    Left ajaxError -> addToast $ ajaxErrorToast "Failed to generate wallet." ajaxError
    Right walletDetails -> do
      assign _walletDetails walletDetails
      handleAction $ OpenCard PickupNewWalletCard

handleAction (WalletNicknameOrIdAction inputFieldAction) = do
  case inputFieldAction of
    InputField.SetValue string -> do
      walletLibrary <- use _walletLibrary
      -- start with nickname validation
      handleAction $ WalletNicknameOrIdAction $ InputField.SetValidator $ walletNicknameError walletLibrary
      -- first check for a matching nickname in the wallet library
      case lookup string walletLibrary of
        Just walletDetails -> do
          toWalletNicknameOrIdInput $ InputField.handleAction $ InputField.SetValue string
          assign _walletDetails walletDetails
          handleAction $ OpenCard PickupWalletCard
        -- then check for a matching ID in the wallet library
        Nothing -> case findMin $ filter (\walletDetails -> UUID.toString (unwrap (view _companionAppId walletDetails)) == string) walletLibrary of
          Just { key, value } -> do
            assign _walletDetails value
            handleAction $ OpenCard PickupWalletCard
          -- then check whether the string is a valid UUID
          Nothing -> case parsePlutusAppId string of
            Just plutusAppId -> do
              ajaxWalletDetails <- lookupWalletDetails plutusAppId
              -- now we know it's a wallet id, switch validator
              toWalletNicknameOrIdInput $ InputField.handleAction $ InputField.SetValidator $ walletIdError ajaxWalletDetails
              case ajaxWalletDetails of
                Left ajaxError -> pure unit
                Right walletDetails -> do
                  assign _walletDetails walletDetails
                  handleAction $ OpenCard PickupWalletCard
            Nothing -> pure unit
    _ -> pure unit
  toWalletNicknameOrIdInput $ InputField.handleAction inputFieldAction

handleAction (SetWalletNickname walletNickname) = assign (_walletDetails <<< _walletNickname) walletNickname

handleAction PickupWallet = do
  walletDetails <- use _walletDetails
  walletNickname <- use (_walletDetails <<< _walletNickname)
  modifying _walletLibrary (insert walletNickname walletDetails)
  walletLibrary <- use _walletLibrary
  liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON walletLibrary
  callMainFrameAction $ MainFrame.EnterPlayState walletLibrary walletDetails

handleAction ClearLocalStorage =
  liftEffect do
    removeItem walletLibraryLocalStorageKey
    removeItem walletDetailsLocalStorageKey
    location_ <- location =<< window
    reload location_

----------
toWalletNicknameOrIdInput ::
  forall m msg slots.
  Functor m =>
  HalogenM (InputField.State WalletNicknameOrIdError) (InputField.Action WalletNicknameOrIdError) slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toWalletNicknameOrIdInput = mapSubmodule _walletNicknameOrIdInput WalletNicknameOrIdAction
