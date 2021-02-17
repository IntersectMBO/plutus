module MainFrame.Lenses
  ( _wallets
  , _newWalletNicknameKey
  , _subState
  , _pickupState
  , _walletState
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
import MainFrame.Types (WalletState, PickupState, State)
import Marlowe.Semantics (PubKey)
import Wallet.Types (WalletLibrary, WalletNicknameKey)

_wallets :: Lens' State WalletLibrary
_wallets = prop (SProxy :: SProxy "wallets")

_newWalletNicknameKey :: Lens' State WalletNicknameKey
_newWalletNicknameKey = prop (SProxy :: SProxy "newWalletNicknameKey")

_subState :: Lens' State (Either PickupState WalletState)
_subState = prop (SProxy :: SProxy "subState")

-- This isn't a Traversal' in any meaningful sense (that I can see), but a Traversal'
-- is a Strong Choice Profunctor, so this is a neat type for the occasion.
-- Alternatively: forall a. Strong a => Choice a => Optic' a State PickupState
_pickupState :: Traversal' State PickupState
_pickupState = _subState <<< _Left

-- As above.
_walletState :: Traversal' State WalletState
_walletState = _subState <<< _Right

_contractState :: Lens' State Contract.State
_contractState = prop (SProxy :: SProxy "contractState")

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

_on :: Lens' WalletState Boolean
_on = prop (SProxy :: SProxy "on")
