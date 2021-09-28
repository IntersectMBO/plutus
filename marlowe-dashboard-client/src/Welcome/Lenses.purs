module Welcome.Lenses
  ( _modal
  , _walletLibrary
  , _walletNicknameOrIdInput
  , _remoteWalletDetails
  , _enteringDashboardState
  ) where

import Prologue
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\))
import InputField.Types (State) as InputField
import Types (WebData)
import Contacts.Types (WalletDetails, WalletLibrary)
import Welcome.Types (Modal, State, WalletNicknameOrIdError)

_modal :: Lens' State (Maybe (Modal /\ Boolean))
_modal = prop (SProxy :: SProxy "modal")

_walletLibrary :: Lens' State WalletLibrary
_walletLibrary = prop (SProxy :: SProxy "walletLibrary")

_walletNicknameOrIdInput :: Lens' State (InputField.State WalletNicknameOrIdError)
_walletNicknameOrIdInput = prop (SProxy :: SProxy "walletNicknameOrIdInput")

_remoteWalletDetails :: Lens' State (WebData WalletDetails)
_remoteWalletDetails = prop (SProxy :: SProxy "remoteWalletDetails")

_enteringDashboardState :: Lens' State Boolean
_enteringDashboardState = prop (SProxy :: SProxy "enteringDashboardState")
