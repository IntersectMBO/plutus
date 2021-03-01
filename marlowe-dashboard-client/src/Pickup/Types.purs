module Pickup.Types
  ( State
  , Screen(..)
  , Card(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Maybe (Maybe(..))
import Marlowe.Semantics (PubKey)
import WalletData.Types (WalletNicknameKey)

type State
  = { screen :: Screen
    , card :: Maybe Card
    }

-- there's only one pickup screen at the moment, but we might need more, and
-- in any case it seems clearer to specify it explicitly
data Screen
  = GDPRScreen
  | GenerateWalletScreen

derive instance eqScreen :: Eq Screen

data Card
  = PickupNewWalletCard
  | PickupWalletCard WalletNicknameKey

derive instance eqCard :: Eq Card

data Action
  = SetScreen Screen
  | SetCard (Maybe Card)
  | GenerateNewWallet
  | LookupWallet String
  | SetNewWalletNickname String
  | PickupNewWallet
  | PickupWallet PubKey

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (SetScreen _) = Just $ defaultEvent "SetPickupScreen"
  toEvent (SetCard _) = Just $ defaultEvent "SetPickupCard"
  toEvent GenerateNewWallet = Just $ defaultEvent "GenerateNewWallet"
  toEvent (LookupWallet _) = Nothing
  toEvent (SetNewWalletNickname _) = Just $ defaultEvent "SetNewWalletNickname"
  toEvent PickupNewWallet = Just $ defaultEvent "PickupNewWallet"
  toEvent (PickupWallet _) = Just $ defaultEvent "PickupWallet"
