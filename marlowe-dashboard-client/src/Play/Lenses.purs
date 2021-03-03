module Play.Lenses
  ( _wallet
  , _menuOpen
  , _templateState
  , _contractState
  ) where

import Contract.Types (State) as Contract
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Marlowe.Semantics (PubKey)
import Play.Types (State)
import Template.Types (State) as Template

_wallet :: Lens' State PubKey
_wallet = prop (SProxy :: SProxy "wallet")

_menuOpen :: Lens' State Boolean
_menuOpen = prop (SProxy :: SProxy "menuOpen")

_templateState :: Lens' State Template.State
_templateState = prop (SProxy :: SProxy "templateState")

_contractState :: Lens' State Contract.State
_contractState = prop (SProxy :: SProxy "contractState")
