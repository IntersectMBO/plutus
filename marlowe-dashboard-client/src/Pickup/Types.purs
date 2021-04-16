module Pickup.Types
  ( State
  , Card(..)
  , PickupNewWalletContext(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Maybe (Maybe(..))
import WalletData.Types (WalletNickname, WalletDetails)

type State
  = { card :: Maybe Card
    , pickupWalletString :: String
    }

data Card
  = PickupNewWalletCard PickupNewWalletContext
  | PickupWalletCard WalletDetails

derive instance eqCard :: Eq Card

data PickupNewWalletContext
  = WalletGenerated
  | WalletFound

derive instance eqPickupNewWalletContext :: Eq PickupNewWalletContext

data Action
  = SetCard (Maybe Card)
  | GenerateNewWallet
  | SetPickupWalletString String
  | SetNewWalletNickname WalletNickname
  | SetNewWalletContractId String
  | PickupNewWallet
  | PickupWallet WalletDetails

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (SetCard _) = Just $ defaultEvent "SetPickupCard"
  toEvent GenerateNewWallet = Just $ defaultEvent "GenerateNewWallet"
  toEvent (SetPickupWalletString _) = Nothing
  toEvent (SetNewWalletNickname _) = Nothing
  toEvent (SetNewWalletContractId _) = Nothing
  toEvent PickupNewWallet = Just $ defaultEvent "PickupWallet"
  toEvent (PickupWallet _) = Just $ defaultEvent "PickupWallet"
