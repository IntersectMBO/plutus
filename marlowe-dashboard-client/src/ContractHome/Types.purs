module ContractHome.Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Contract.Types (State) as Contract
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Types (ContractInstanceId)

data ContractStatus
  = Running
  | Completed

derive instance eqContractStatus :: Eq ContractStatus

type State
  = { status :: ContractStatus
    -- FIXME: We need to see if the performance hit of having to split the map between running
    --        and completed is worth not having state duplication (Two arrays and a Map). Also,
    --        we should check if this data belongs here or in Play.State.
    , contracts :: Map ContractInstanceId Contract.State
    , selectedContractIndex :: Maybe ContractInstanceId
    }

type PartitionedContracts
  = { completed :: Array Contract.State, running :: Array Contract.State }

data Action
  = OpenTemplateLibraryCard
  | SelectView ContractStatus
  | OpenContract ContractInstanceId

instance actionIsEvent :: IsEvent Action where
  toEvent OpenTemplateLibraryCard = Just $ defaultEvent "OpenTemplateLibraryCard"
  toEvent (SelectView _) = Just $ defaultEvent "SelectView"
  toEvent (OpenContract _) = Just $ defaultEvent "OpenContract"
