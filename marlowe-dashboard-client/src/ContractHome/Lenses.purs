module ContractHome.Lenses
  ( _status
  , _contracts
  , _selectedContract
  ) where

import Contract.Types (State) as Contract
import ContractHome.Types (ContractStatus, State)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))

_status :: Lens' State ContractStatus
_status = prop (SProxy :: SProxy "status")

_contracts :: Lens' State (Array Contract.State)
_contracts = prop (SProxy :: SProxy "contracts")

_selectedContract :: Lens' State (Maybe Contract.State)
_selectedContract = prop (SProxy :: SProxy "selectedContract")
