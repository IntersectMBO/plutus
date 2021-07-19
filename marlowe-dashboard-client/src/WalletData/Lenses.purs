module WalletData.Lenses
  ( _walletLibrary
  , _cardSection
  , _walletNicknameInput
  , _walletIdInput
  , _remoteWalletInfo
  , _walletNickname
  , _companionAppId
  , _marloweAppId
  , _walletInfo
  , _assets
  , _previousCompanionAppState
  , _wallet
  , _pubKey
  , _pubKeyHash
  ) where

import Prelude
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import InputField.Types (State) as InputField
import Marlowe.PAB (MarloweData, MarloweParams, PlutusAppId)
import Marlowe.Semantics (Assets, PubKey)
import Types (WebData)
import WalletData.Types (CardSection, PubKeyHash, State, Wallet, WalletIdError, WalletInfo, WalletLibrary, WalletNickname, WalletNicknameError, WalletDetails)

_walletLibrary :: Lens' State WalletLibrary
_walletLibrary = prop (SProxy :: SProxy "walletLibrary")

_cardSection :: Lens' State CardSection
_cardSection = prop (SProxy :: SProxy "cardSection")

_walletNicknameInput :: Lens' State (InputField.State WalletNicknameError)
_walletNicknameInput = prop (SProxy :: SProxy "walletNicknameInput")

_walletIdInput :: Lens' State (InputField.State WalletIdError)
_walletIdInput = prop (SProxy :: SProxy "walletIdInput")

_remoteWalletInfo :: Lens' State (WebData WalletInfo)
_remoteWalletInfo = prop (SProxy :: SProxy "remoteWalletInfo")

------------------------------------------------------------
_walletNickname :: Lens' WalletDetails WalletNickname
_walletNickname = prop (SProxy :: SProxy "walletNickname")

_companionAppId :: Lens' WalletDetails PlutusAppId
_companionAppId = prop (SProxy :: SProxy "companionAppId")

_marloweAppId :: Lens' WalletDetails PlutusAppId
_marloweAppId = prop (SProxy :: SProxy "marloweAppId")

_walletInfo :: Lens' WalletDetails WalletInfo
_walletInfo = prop (SProxy :: SProxy "walletInfo")

_assets :: Lens' WalletDetails Assets
_assets = prop (SProxy :: SProxy "assets")

_previousCompanionAppState :: Lens' WalletDetails (Maybe (Map MarloweParams MarloweData))
_previousCompanionAppState = prop (SProxy :: SProxy "previousCompanionAppState")

------------------------------------------------------------
_wallet :: Lens' WalletInfo Wallet
_wallet = _Newtype <<< prop (SProxy :: SProxy "wallet")

_pubKey :: Lens' WalletInfo PubKey
_pubKey = _Newtype <<< prop (SProxy :: SProxy "pubKey")

_pubKeyHash :: Lens' WalletInfo PubKeyHash
_pubKeyHash = _Newtype <<< prop (SProxy :: SProxy "pubKeyHash")
