module Play.Lenses
  ( _allContracts
  , _walletDetails
  , _menuOpen
  , _currentSlot
  , _templateState
  , _contractsState
  , _selectedContract
  ) where

import Prelude
import Contract.Types (State) as Contract
import ContractHome.Lenses (_contracts, _selectedContractIndex)
import ContractHome.Types (State) as ContractHome
import Data.Array as Array
import Data.Lens (Lens', Traversal', set, view, wander)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Symbol (SProxy(..))
import Marlowe.Semantics (Slot)
import Play.Types (State)
import Template.Types (State) as Template
import WalletData.Types (WalletDetails)

_walletDetails :: Lens' State WalletDetails
_walletDetails = prop (SProxy :: SProxy "walletDetails")

_menuOpen :: Lens' State Boolean
_menuOpen = prop (SProxy :: SProxy "menuOpen")

_currentSlot :: Lens' State Slot
_currentSlot = prop (SProxy :: SProxy "currentSlot")

_templateState :: Lens' State Template.State
_templateState = prop (SProxy :: SProxy "templateState")

_contractsState :: Lens' State ContractHome.State
_contractsState = prop (SProxy :: SProxy "contractsState")

_allContracts :: Lens' State (Array Contract.State)
_allContracts = _contractsState <<< _contracts

-- This traversal focus on a specific contract indexed by another property of the state
_selectedContract :: Traversal' State Contract.State
_selectedContract =
  wander \f state -> case view (_contractsState <<< _selectedContractIndex) state of
    Just ix
      | Just contract <- Array.index (view _allContracts state) ix ->
        let
          updateContract contract' = fromMaybe (view _allContracts state) $ Array.updateAt ix contract' state.contractsState.contracts
        in
          (\contract' -> set _allContracts (updateContract contract') state) <$> f contract
    _ -> pure state
