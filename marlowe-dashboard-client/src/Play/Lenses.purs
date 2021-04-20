module Play.Lenses
  ( _walletDetails
  , _menuOpen
  , _cards
  , _currentSlot
  , _slotsInSync
  , _templateState
  , _contractsState
  , _allContracts
  , _selectedContract
  ) where

import Prelude
import Contract.Types (State) as Contract
import ContractHome.Lenses (_contracts, _selectedContract) as ContractHome
import ContractHome.Types (State) as ContractHome
import Data.Lens (Lens', Traversal')
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Symbol (SProxy(..))
import Marlowe.Semantics (Slot)
import Play.Types (Card, State)
import Template.Types (State) as Template
import WalletData.Types (WalletDetails)
import Types (ContractInstanceId)

_walletDetails :: Lens' State WalletDetails
_walletDetails = prop (SProxy :: SProxy "walletDetails")

_menuOpen :: Lens' State Boolean
_menuOpen = prop (SProxy :: SProxy "menuOpen")

_cards :: Lens' State (Array Card)
_cards = prop (SProxy :: SProxy "cards")

_currentSlot :: Lens' State Slot
_currentSlot = prop (SProxy :: SProxy "currentSlot")

_slotsInSync :: Lens' State Boolean
_slotsInSync = prop (SProxy :: SProxy "slotsInSync")

_templateState :: Lens' State Template.State
_templateState = prop (SProxy :: SProxy "templateState")

_contractsState :: Lens' State ContractHome.State
_contractsState = prop (SProxy :: SProxy "contractsState")

_allContracts :: Lens' State (Map ContractInstanceId Contract.State)
_allContracts = _contractsState <<< ContractHome._contracts

-- This traversal focus on a specific contract indexed by another property of the state
_selectedContract :: Traversal' State Contract.State
_selectedContract = _contractsState <<< ContractHome._selectedContract
