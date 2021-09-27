module Welcome.Lenses
  ( _modal
  , _walletLibrary
  , _walletNicknameOrIdInput
  , _walletNicknameInput
  , _walletId
  , _remoteWalletDetails
  , _enteringDashboardState
  ) where

import Component.Modal.Types as Modal
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import InputField.Types (State) as InputField
import Marlowe.PAB (PlutusAppId)
import Types (WebData)
import Contacts.Types (WalletDetails, WalletLibrary, WalletNicknameError)
import Welcome.Types (Modal, State, WalletNicknameOrIdError)

_modal :: Lens' State (Modal.State Modal)
_modal = prop (SProxy :: SProxy "modal")

_walletLibrary :: Lens' State WalletLibrary
_walletLibrary = prop (SProxy :: SProxy "walletLibrary")

_walletNicknameOrIdInput :: Lens' State (InputField.State WalletNicknameOrIdError)
_walletNicknameOrIdInput = prop (SProxy :: SProxy "walletNicknameOrIdInput")

_walletNicknameInput :: Lens' State (InputField.State WalletNicknameError)
_walletNicknameInput = prop (SProxy :: SProxy "walletNicknameInput")

_walletId :: Lens' State PlutusAppId
_walletId = prop (SProxy :: SProxy "walletId")

_remoteWalletDetails :: Lens' State (WebData WalletDetails)
_remoteWalletDetails = prop (SProxy :: SProxy "remoteWalletDetails")

_enteringDashboardState :: Lens' State Boolean
_enteringDashboardState = prop (SProxy :: SProxy "enteringDashboardState")
