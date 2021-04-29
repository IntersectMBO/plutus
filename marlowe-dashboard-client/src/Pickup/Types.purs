module Pickup.Types
  ( State
  , Card(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Maybe (Maybe(..))
import WalletData.Types (WalletDetails, WalletLibrary, WalletNickname)

type State
  = { card :: Maybe Card
    , walletLibrary :: WalletLibrary
    , pickupWalletString :: String
    , walletDetails :: WalletDetails
    , pickingUp :: Boolean -- true when we are in the process of picking up a wallet
    }

data Card
  = PickupNewWalletCard
  | PickupWalletCard

derive instance eqCard :: Eq Card

data Action
  = OpenCard Card
  | CloseCard
  | GenerateWallet
  | SetPickupWalletString String
  | SetWalletNickname WalletNickname
  | PickupWallet

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (OpenCard _) = Nothing
  toEvent CloseCard = Nothing
  toEvent GenerateWallet = Just $ defaultEvent "GenerateWallet"
  toEvent (SetPickupWalletString _) = Nothing
  toEvent (SetWalletNickname _) = Nothing
  toEvent PickupWallet = Just $ defaultEvent "PickupWallet"
