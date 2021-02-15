module MainFrame.Lenses
  ( _wallets
  , _newWalletNicknameKey
  , _outsideCard
  , _insideState
  , _contractState
  , _wallet
  , _menuOpen
  , _screen
  , _card
  , _on
  ) where

import Contract.Types (State) as Contract
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import MainFrame.Types (Card, InsideState, OutsideCard, Screen, State)
import Wallet.Types (PubKeyHash, WalletLibrary, WalletNicknameKey)

_wallets :: Lens' State WalletLibrary
_wallets = prop (SProxy :: SProxy "wallets")

_newWalletNicknameKey :: Lens' State WalletNicknameKey
_newWalletNicknameKey = prop (SProxy :: SProxy "newWalletNicknameKey")

_outsideCard :: Lens' State (Maybe OutsideCard)
_outsideCard = prop (SProxy :: SProxy "outsideCard")

_insideState :: Lens' State (Maybe InsideState)
_insideState = prop (SProxy :: SProxy "insideState")

_contractState :: Lens' State Contract.State
_contractState = prop (SProxy :: SProxy "contractState")

------------------------------------------------------------
_wallet :: Lens' InsideState PubKeyHash
_wallet = prop (SProxy :: SProxy "wallet")

_menuOpen :: Lens' InsideState Boolean
_menuOpen = prop (SProxy :: SProxy "menuOpen")

_screen :: Lens' InsideState Screen
_screen = prop (SProxy :: SProxy "screen")

_card :: Lens' InsideState (Maybe Card)
_card = prop (SProxy :: SProxy "card")

_on :: Lens' InsideState Boolean
_on = prop (SProxy :: SProxy "on")
