module Page.Welcome.Lenses
  ( _card
  , _cardOpen
  , _walletLibrary
  , _walletNicknameOrIdInput
  , _walletNicknameInput
  , _walletId
  , _remoteWalletDetails
  , _enteringDashboardState
  ) where

import Prologue
import Component.Contacts.Types (WalletDetails, WalletLibrary, WalletNicknameError)
import Component.InputField.Types (State) as InputField
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Marlowe.PAB (PlutusAppId)
import Page.Welcome.Types (Card, State, WalletNicknameOrIdError)
import Types (WebData)

_card :: Lens' State (Maybe Card)
_card = prop (SProxy :: SProxy "card")

_cardOpen :: Lens' State Boolean
_cardOpen = prop (SProxy :: SProxy "cardOpen")

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
