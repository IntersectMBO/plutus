module WalletData.Lenses
  ( _walletNicknameString
  , _contractInstanceIdString
  , _remoteDataWalletInfo
  , _remoteDataAssets
  , _walletNickname
  , _contractInstanceId
  , _wallet
  , _pubKey
  , _pubKeyHash
  , _assets
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Marlowe.Semantics (Assets, PubKey)
import Types (ContractInstanceId, WebData)
import WalletData.Types (NewWalletDetails, PubKeyHash, Wallet, WalletDetails, WalletInfo, WalletNickname)

_walletNicknameString :: Lens' NewWalletDetails String
_walletNicknameString = prop (SProxy :: SProxy "walletNicknameString")

_contractInstanceIdString :: Lens' NewWalletDetails String
_contractInstanceIdString = prop (SProxy :: SProxy "contractInstanceIdString")

_remoteDataWalletInfo :: Lens' NewWalletDetails (WebData WalletInfo)
_remoteDataWalletInfo = prop (SProxy :: SProxy "remoteDataWalletInfo")

_remoteDataAssets :: Lens' NewWalletDetails (WebData Assets)
_remoteDataAssets = prop (SProxy :: SProxy "remoteDataAssets")

------------------------------------------------------------
_walletNickname :: Lens' WalletDetails WalletNickname
_walletNickname = prop (SProxy :: SProxy "walletNickname")

_contractInstanceId :: Lens' WalletDetails ContractInstanceId
_contractInstanceId = prop (SProxy :: SProxy "contractInstanceId")

_wallet :: Lens' WalletDetails Wallet
_wallet = prop (SProxy :: SProxy "wallet")

_pubKey :: Lens' WalletDetails PubKey
_pubKey = prop (SProxy :: SProxy "pubKey")

_pubKeyHash :: Lens' WalletDetails PubKeyHash
_pubKeyHash = prop (SProxy :: SProxy "pubKeyHash")

_assets :: Lens' WalletDetails Assets
_assets = prop (SProxy :: SProxy "assets")
