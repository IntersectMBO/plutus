module Pickup.Types
  ( State
  , Card(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Data.Maybe (Maybe(..))
import InputField.Types (Action, State) as InputField
import Pickup.Validation (WalletNicknameOrIdError)
import WalletData.Types (WalletDetails, WalletLibrary, WalletNickname)

type State
  = { card :: Maybe Card
    , walletLibrary :: WalletLibrary
    , walletNicknameOrIdInput :: InputField.State WalletNicknameOrIdError
    , walletDetails :: WalletDetails
    , pickingUp :: Boolean -- true when we are in the process of picking up a wallet
    }

data Card
  = PickupNewWalletCard
  | PickupWalletCard
  | LocalWalletMissingCard

derive instance eqCard :: Eq Card

data Action
  = OpenCard Card
  | CloseCard
  | GenerateWallet
  | WalletNicknameOrIdAction (InputField.Action WalletNicknameOrIdError)
  | SetWalletNickname WalletNickname
  | PickupWallet
  | ClearLocalStorage

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (OpenCard _) = Nothing
  toEvent CloseCard = Nothing
  toEvent GenerateWallet = Just $ defaultEvent "GenerateWallet"
  toEvent (WalletNicknameOrIdAction inputFieldAction) = toEvent inputFieldAction
  toEvent (SetWalletNickname _) = Nothing
  toEvent PickupWallet = Just $ defaultEvent "PickupWallet"
  toEvent ClearLocalStorage = Just $ defaultEvent "ClearLocalStorage"
