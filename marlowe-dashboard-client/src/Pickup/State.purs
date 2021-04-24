module Pickup.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe (class ManageMarlowe, marloweCreateWallet, marloweLookupWallet)
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
import LocalStorage (setItem)
import MainFrame.Types (ChildSlots, Msg)
import MainFrame.Types (Action(..)) as MainFrame
import Pickup.Lenses (_card, _pickupWalletString, _walletDetails, _walletLibrary)
import Pickup.Types (Action(..), Card(..), State)
import StaticData (walletLibraryLocalStorageKey)
import Toast.Types (ajaxErrorToast)
import WalletData.Lenses (_companionContractId, _walletNickname)
import WalletData.State (defaultWalletDetails)
import WalletData.Types (WalletLibrary)
import WalletData.Validation (parseContractInstanceId)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty

mkInitialState :: WalletLibrary -> State
mkInitialState walletLibrary =
  { walletLibrary
  , card: Nothing
  , pickupWalletString: mempty
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
  ajaxWallet <- marloweCreateWallet
  case ajaxWallet of
    Left ajaxError -> addToast $ ajaxErrorToast "Failed to generate wallet." ajaxError
    Right walletDetails -> do
      assign _walletDetails walletDetails
      handleAction $ OpenCard PickupNewWalletCard

handleAction (SetPickupWalletString string) = do
  assign _pickupWalletString string
  walletLibrary <- use _walletLibrary
  -- first check for a matching nickname in the wallet library
  case lookup string walletLibrary of
    Just walletDetails -> do
      assign _walletDetails walletDetails
      handleAction $ OpenCard PickupWalletCard
    -- then check for a matching ID in the wallet library
    Nothing -> case findMin $ filter (\walletDetails -> UUID.toString (unwrap (view _companionContractId walletDetails)) == string) walletLibrary of
      Just { key, value } -> do
        assign _walletDetails value
        handleAction $ OpenCard PickupWalletCard
      -- then check whether the string is a valid UUID
      Nothing -> case parseContractInstanceId string of
        Just contractInstanceId -> do
          ajaxWalletDetails <- marloweLookupWallet contractInstanceId
          case ajaxWalletDetails of
            Left ajaxError -> pure unit -- TODO: show negative feedback to the user
            Right walletDetails -> do
              assign _walletDetails walletDetails
              handleAction $ OpenCard PickupWalletCard
        Nothing -> pure unit -- TODO: show negative feedback to the user

handleAction (SetWalletNickname walletNickname) = assign (_walletDetails <<< _walletNickname) walletNickname

handleAction PickupWallet = do
  walletDetails <- use _walletDetails
  walletNickname <- use (_walletDetails <<< _walletNickname)
  modifying _walletLibrary (insert walletNickname walletDetails)
  walletLibrary <- use _walletLibrary
  liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON walletLibrary
  callMainFrameAction $ MainFrame.EnterPlayState walletLibrary walletDetails
