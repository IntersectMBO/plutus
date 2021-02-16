module MainFrame.Lenses
  ( _wallets
  , _newWalletNicknameKey
  , _subState
  , _outsideState
  , _insideState
  , _contractState
  , _screen
  , _card
  , _wallet
  , _menuOpen
  , _on
  ) where

import Prelude
import Contract.Types (State) as Contract
import Data.Either (Either)
import Data.Lens (Lens', Traversal')
import Data.Lens.Prism.Either (_Left, _Right)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import MainFrame.Types (InsideState, OutsideState, State)
import Wallet.Types (PubKeyHash, WalletLibrary, WalletNicknameKey)

_wallets :: Lens' State WalletLibrary
_wallets = prop (SProxy :: SProxy "wallets")

_newWalletNicknameKey :: Lens' State WalletNicknameKey
_newWalletNicknameKey = prop (SProxy :: SProxy "newWalletNicknameKey")

_subState :: Lens' State (Either OutsideState InsideState)
_subState = prop (SProxy :: SProxy "subState")

_outsideState :: Traversal' State OutsideState
_outsideState = _subState <<< _Left

_insideState :: Traversal' State InsideState
_insideState = _subState <<< _Right

_contractState :: Lens' State Contract.State
_contractState = prop (SProxy :: SProxy "contractState")

------------------------------------------------------------
_screen :: forall s b. Lens' { screen :: s | b } s
_screen = prop (SProxy :: SProxy "screen")

_card :: forall c b. Lens' { card :: c | b } c
_card = prop (SProxy :: SProxy "card")

------------------------------------------------------------
_wallet :: Lens' InsideState PubKeyHash
_wallet = prop (SProxy :: SProxy "wallet")

_menuOpen :: Lens' InsideState Boolean
_menuOpen = prop (SProxy :: SProxy "menuOpen")

_on :: Lens' InsideState Boolean
_on = prop (SProxy :: SProxy "on")
