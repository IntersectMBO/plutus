module Pickup.Types
  ( State
  , Card(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Maybe (Maybe(..))
import WalletData.Types (WalletNickname, WalletDetails)

type State
  = { card :: Maybe Card
    }

data Card
  = PickupNewWalletCard
  | PickupWalletCard WalletDetails

derive instance eqCard :: Eq Card

data Action
  = SetCard (Maybe Card)
  | GenerateNewWallet
  | LookupWallet String
  | SetNewWalletNickname WalletNickname
  | SetNewWalletContractId String
  | PickupNewWallet
  | PickupWallet WalletDetails

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (SetCard _) = Just $ defaultEvent "SetPickupCard"
  toEvent GenerateNewWallet = Just $ defaultEvent "GenerateNewWallet"
  toEvent (LookupWallet _) = Nothing
  toEvent (SetNewWalletNickname _) = Nothing
  toEvent (SetNewWalletContractId _) = Nothing
  toEvent PickupNewWallet = Just $ defaultEvent "PickupWallet"
  toEvent (PickupWallet _) = Just $ defaultEvent "PickupWallet"
