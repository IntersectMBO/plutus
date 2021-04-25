module ContractHome.State
  ( dummyState
  , mkInitialState
  , historyToContractState
  , handleAction
  , partitionContracts
  ) where

import Prelude
import Contract.State (applyTimeout, isContractClosed)
import Contract.State (dummyState) as Contract
import Contract.Types (State) as Contract
import ContractHome.Lenses (_selectedContractIndex, _status)
import ContractHome.Types (Action(..), ContractStatus(..), State, PartitionedContracts)
import Data.Array as Array
import Data.Lens (assign, filtered, over, traversed)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (snd)
import Halogen (HalogenM, modify_)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.PAB (ContractInstanceId, History)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState mempty

mkInitialState :: Map ContractInstanceId History -> State
mkInitialState contracts =
  { status: Running
  , contracts: map historyToContractState contracts
  , selectedContractIndex: Nothing
  }

-- FIXME: get Contract.State from contract History
historyToContractState :: History -> Contract.State
historyToContractState history = Contract.dummyState

handleAction ::
  forall m.
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction OpenTemplateLibraryCard = pure unit -- handled in Play.State

handleAction (SelectView view) = assign _status view

handleAction (OpenContract ix) = assign _selectedContractIndex $ Just ix

partitionContracts :: Map ContractInstanceId Contract.State -> PartitionedContracts
partitionContracts contracts =
  Map.toUnfoldableUnordered contracts
    # map snd
    # Array.partition isContractClosed
    # \{ no, yes } -> { completed: yes, running: no }
