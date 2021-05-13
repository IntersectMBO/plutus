module Pickup.Lenses
  ( _card
  , _walletLibrary
  , _walletNicknameOrId
  , _walletNicknameInput
  , _walletIdInput
  , _remoteWalletDetails
  , _pickingUp
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import InputField.Types (State) as InputField
import Pickup.Types (Card, State)
import Types (WebData)
import WalletData.Types (WalletDetails, WalletLibrary)
import WalletData.Validation (WalletIdError, WalletNicknameError)

_card :: Lens' State (Maybe Card)
_card = prop (SProxy :: SProxy "card")

_walletLibrary :: Lens' State WalletLibrary
_walletLibrary = prop (SProxy :: SProxy "walletLibrary")

_walletNicknameOrId :: Lens' State String
_walletNicknameOrId = prop (SProxy :: SProxy "walletNicknameOrId")

_walletNicknameInput :: Lens' State (InputField.State WalletNicknameError)
_walletNicknameInput = prop (SProxy :: SProxy "walletNicknameInput")

_walletIdInput :: Lens' State (InputField.State WalletIdError)
_walletIdInput = prop (SProxy :: SProxy "walletIdInput")

_remoteWalletDetails :: Lens' State (WebData WalletDetails)
_remoteWalletDetails = prop (SProxy :: SProxy "remoteWalletDetails")

_pickingUp :: Lens' State Boolean
_pickingUp = prop (SProxy :: SProxy "pickingUp")
