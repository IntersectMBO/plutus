module WalletData.Types
  ( WalletLibrary
  , Nickname
  , WalletDetails
  ) where

import Data.Map (Map)
import Marlowe.Semantics (Assets, PubKey)
import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)

type WalletLibrary
  = Map Nickname WalletDetails

type Nickname
  = String

type WalletDetails
  = { nickname :: Nickname
    , contractId :: String
    , pubKey :: PubKey
    , balance :: RemoteData AjaxError (Array Assets)
    }
