module Pickup.Types
  ( State
  , Card(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Data.Maybe (Maybe(..))
import InputField.Types (Action, State) as InputField
import Types (WebData)
import WalletData.Types (WalletDetails, WalletLibrary, WalletNickname)
import WalletData.Validation (WalletIdError, WalletNicknameError)

type State
  = { card :: Maybe Card
    , walletLibrary :: WalletLibrary
    , walletNicknameOrId :: String
    , walletDropdownOpen :: Boolean
    , walletNicknameInput :: InputField.State WalletNicknameError
    , walletIdInput :: InputField.State WalletIdError
    , remoteWalletDetails :: WebData WalletDetails
    , pickingUp :: Boolean -- true when we are in the process of picking up a wallet
    }

data Card
  = PickupNewWalletCard
  | PickupWalletCard
  | LocalWalletMissingCard

derive instance eqCard :: Eq Card

data Action
  = OpenCard Card
  | CloseCard Card
  | GenerateWallet
  | SetWalletNicknameOrId String
  | SetWalletDropdownOpen Boolean
  | OpenPickupWalletCardWithDetails WalletDetails
  | WalletNicknameInputAction (InputField.Action WalletNicknameError)
  | WalletIdInputAction (InputField.Action WalletIdError)
  | PickupWallet WalletNickname
  | ClearLocalStorage

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (OpenCard _) = Nothing
  toEvent (CloseCard _) = Nothing
  toEvent GenerateWallet = Just $ defaultEvent "GenerateWallet"
  toEvent (SetWalletNicknameOrId _) = Nothing
  toEvent (SetWalletDropdownOpen _) = Nothing
  toEvent (OpenPickupWalletCardWithDetails _) = Nothing
  toEvent (WalletNicknameInputAction inputFieldAction) = toEvent inputFieldAction
  toEvent (WalletIdInputAction inputFieldAction) = toEvent inputFieldAction
  toEvent (PickupWallet _) = Just $ defaultEvent "PickupWallet"
  toEvent ClearLocalStorage = Just $ defaultEvent "ClearLocalStorage"
