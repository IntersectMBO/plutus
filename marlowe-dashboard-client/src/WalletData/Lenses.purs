module WalletData.Lenses
  ( _walletNicknameString
  , _contractInstanceIdString
  , _remoteDataWallet
  , _remoteDataPubKey
  , _remoteDataAssets
  , _walletNickname
  , _contractInstanceId
  , _wallet
  , _pubKey
  , _assets
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import MainFrame.Types (WebData)
import Marlowe.Semantics (Assets, PubKey)
import Marlowe.Types (ContractInstanceId)
import WalletData.Types (NewWalletDetails, Wallet, WalletDetails, WalletNickname)

_walletNicknameString :: Lens' NewWalletDetails String
_walletNicknameString = prop (SProxy :: SProxy "walletNicknameString")

_contractInstanceIdString :: Lens' NewWalletDetails String
_contractInstanceIdString = prop (SProxy :: SProxy "contractInstanceIdString")

_remoteDataWallet :: Lens' NewWalletDetails (WebData Wallet)
_remoteDataWallet = prop (SProxy :: SProxy "remoteDataWallet")

_remoteDataPubKey :: Lens' NewWalletDetails (WebData PubKey)
_remoteDataPubKey = prop (SProxy :: SProxy "remoteDataPubKey")

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

_assets :: Lens' WalletDetails Assets
_assets = prop (SProxy :: SProxy "assets")
