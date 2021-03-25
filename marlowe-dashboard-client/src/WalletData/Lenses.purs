module WalletData.Lenses
  ( _walletNicknameString
  , _contractInstanceIdString
  , _remoteDataWallet
  , _remoteDataPubKey
  , _walletNickname
  , _contractInstanceId
  , _wallet
  , _pubKey
  , _assets
  , _contractInstanceIdAsString
  ) where

import Prelude
import Data.Json.JsonUUID (_JsonUUID)
import Data.Lens (Getter', Lens', to)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Data.UUID (toString) as UUID
import Marlowe.Semantics (Assets, PubKey)
import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Types (ContractInstanceId)
import WalletData.Types (NewWalletDetails, WalletDetails, WalletNickname)

_walletNicknameString :: Lens' NewWalletDetails String
_walletNicknameString = prop (SProxy :: SProxy "walletNicknameString")

_contractInstanceIdString :: Lens' NewWalletDetails String
_contractInstanceIdString = prop (SProxy :: SProxy "contractInstanceIdString")

_remoteDataWallet :: Lens' NewWalletDetails (RemoteData AjaxError Wallet)
_remoteDataWallet = prop (SProxy :: SProxy "remoteDataWallet")

_remoteDataPubKey :: Lens' NewWalletDetails (RemoteData AjaxError PubKey)
_remoteDataPubKey = prop (SProxy :: SProxy "remoteDataPubKey")

------------------------------------------------------------
_walletNickname :: Lens' WalletDetails WalletNickname
_walletNickname = prop (SProxy :: SProxy "walletNickname")

_contractInstanceId :: Lens' WalletDetails ContractInstanceId
_contractInstanceId = prop (SProxy :: SProxy "contractInstanceId")

_wallet :: Lens' WalletDetails Wallet
_wallet = prop (SProxy :: SProxy "wallet")

_pubKey :: Lens' WalletDetails PubKey
_pubKey = prop (SProxy :: SProxy "pubKey")

_assets :: Lens' WalletDetails Assets
_assets = prop (SProxy :: SProxy "assets")

----------
_contractInstanceIdAsString :: Getter' ContractInstanceId String
_contractInstanceIdAsString = _Newtype <<< prop (SProxy :: SProxy "unContractInstanceId") <<< _JsonUUID <<< to UUID.toString
