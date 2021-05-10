module Pickup.Lenses
  ( _card
  , _walletLibrary
  , _walletNicknameOrIdInput
  , _walletDetails
  , _pickingUp
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import InputField.Types (State) as InputField
import Pickup.Types (Card, State)
import Pickup.Validation (WalletNicknameOrIdError)
import WalletData.Types (WalletDetails, WalletLibrary)

_card :: Lens' State (Maybe Card)
_card = prop (SProxy :: SProxy "card")

_walletLibrary :: Lens' State WalletLibrary
_walletLibrary = prop (SProxy :: SProxy "walletLibrary")

_walletNicknameOrIdInput :: Lens' State (InputField.State WalletNicknameOrIdError)
_walletNicknameOrIdInput = prop (SProxy :: SProxy "walletNicknameOrIdInput")

_walletDetails :: Lens' State WalletDetails
_walletDetails = prop (SProxy :: SProxy "walletDetails")

_pickingUp :: Lens' State Boolean
_pickingUp = prop (SProxy :: SProxy "pickingUp")
