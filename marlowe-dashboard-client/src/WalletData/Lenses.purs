module WalletData.Lenses
  ( _nickname
  , _contractId
  , _balance
  , _pubKey
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Marlowe.Semantics (Assets, PubKey)
import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)
import WalletData.Types (Nickname, WalletDetails)

_nickname :: Lens' WalletDetails Nickname
_nickname = prop (SProxy :: SProxy "nickname")

_pubKey :: Lens' WalletDetails PubKey
_pubKey = prop (SProxy :: SProxy "pubKey")

_contractId :: forall r. Lens' { contractId :: String | r } String
_contractId = prop (SProxy :: SProxy "contractId")

_balance :: Lens' WalletDetails (RemoteData AjaxError (Array Assets))
_balance = prop (SProxy :: SProxy "balance")
