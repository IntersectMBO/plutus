module Play.Lenses
  ( _walletDetails
  , _menuOpen
  , _templateState
  , _contractsState
  ) where

import ContractHome.Types (State) as ContractHome
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import WalletData.Types (WalletDetails)
import Play.Types (State)
import Template.Types (State) as Template

_walletDetails :: Lens' State WalletDetails
_walletDetails = prop (SProxy :: SProxy "walletDetails")

_menuOpen :: Lens' State Boolean
_menuOpen = prop (SProxy :: SProxy "menuOpen")

_templateState :: Lens' State Template.State
_templateState = prop (SProxy :: SProxy "templateState")

_contractsState :: Lens' State ContractHome.State
_contractsState = prop (SProxy :: SProxy "contractsState")
