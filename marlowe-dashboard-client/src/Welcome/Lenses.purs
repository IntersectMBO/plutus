module Welcome.Lenses
  ( _card
  , _walletLibrary
  , _walletNicknameOrIdInput
  , _walletNicknameInput
  , _walletIdInput
  , _remoteWalletDetails
  , _connecting
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import InputField.Types (State) as InputField
import Types (WebData)
import WalletData.Types (WalletDetails, WalletLibrary)
import WalletData.Validation (WalletIdError, WalletNicknameError, WalletNicknameOrIdError)
import Welcome.Types (Card, State)

_card :: Lens' State (Maybe Card)
_card = prop (SProxy :: SProxy "card")

_walletLibrary :: Lens' State WalletLibrary
_walletLibrary = prop (SProxy :: SProxy "walletLibrary")

_walletNicknameOrIdInput :: Lens' State (InputField.State WalletNicknameOrIdError)
_walletNicknameOrIdInput = prop (SProxy :: SProxy "walletNicknameOrIdInput")

_walletNicknameInput :: Lens' State (InputField.State WalletNicknameError)
_walletNicknameInput = prop (SProxy :: SProxy "walletNicknameInput")

_walletIdInput :: Lens' State (InputField.State WalletIdError)
_walletIdInput = prop (SProxy :: SProxy "walletIdInput")

_remoteWalletDetails :: Lens' State (WebData WalletDetails)
_remoteWalletDetails = prop (SProxy :: SProxy "remoteWalletDetails")

_connecting :: Lens' State Boolean
_connecting = prop (SProxy :: SProxy "connecting")
