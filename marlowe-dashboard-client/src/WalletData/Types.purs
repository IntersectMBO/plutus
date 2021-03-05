module WalletData.Types
  ( WalletLibrary
  , Nickname
  , WalletDetails
  ) where

import Data.Map (Map)
import Data.Maybe (Maybe)
import Marlowe.Semantics (Assets, PubKey)

type WalletLibrary
  = Map Nickname WalletDetails

type Nickname
  = String

type WalletDetails
  = { nickname :: Nickname
    , contractId :: String
    , pubKey :: PubKey
    , balance :: Maybe (Array Assets)
    }
