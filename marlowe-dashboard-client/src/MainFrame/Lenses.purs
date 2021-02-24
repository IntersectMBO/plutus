module MainFrame.Lenses
  ( _wallets
  , _newWalletNicknameKey
  , _templates
  , _subState
  , _pickupState
  , _walletState
  , _screen
  , _card
  , _wallet
  , _menuOpen
  , _webSocketStatus
  , _templateState
  , _contractState
  ) where

import Prelude
import Contract.Types (State) as Contract
import Data.Either (Either)
import Data.Lens (Lens', Traversal')
import Data.Lens.Prism.Either (_Left, _Right)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import MainFrame.Types (PickupState, State, WalletState, WebSocketStatus)
import Marlowe.Semantics (PubKey)
import Template.Types (State, Template) as Template
import WalletData.Types (WalletLibrary, WalletNicknameKey)

_wallets :: Lens' State WalletLibrary
_wallets = prop (SProxy :: SProxy "wallets")

_newWalletNicknameKey :: Lens' State WalletNicknameKey
_newWalletNicknameKey = prop (SProxy :: SProxy "newWalletNicknameKey")

_templates :: Lens' State (Array Template.Template)
_templates = prop (SProxy :: SProxy "templates")

_subState :: Lens' State (Either PickupState WalletState)
_subState = prop (SProxy :: SProxy "subState")

_webSocketStatus :: Lens' State WebSocketStatus
_webSocketStatus = prop (SProxy :: SProxy "webSocketStatus")

------------------------------------------------------------
_pickupState :: Traversal' State PickupState
_pickupState = _subState <<< _Left

_walletState :: Traversal' State WalletState
_walletState = _subState <<< _Right

------------------------------------------------------------
_screen :: forall s b. Lens' { screen :: s | b } s
_screen = prop (SProxy :: SProxy "screen")

_card :: forall c b. Lens' { card :: c | b } c
_card = prop (SProxy :: SProxy "card")

------------------------------------------------------------
_wallet :: Lens' WalletState PubKey
_wallet = prop (SProxy :: SProxy "wallet")

_menuOpen :: Lens' WalletState Boolean
_menuOpen = prop (SProxy :: SProxy "menuOpen")

_templateState :: Lens' WalletState Template.State
_templateState = prop (SProxy :: SProxy "templateState")

_contractState :: Lens' WalletState Contract.State
_contractState = prop (SProxy :: SProxy "contractState")
