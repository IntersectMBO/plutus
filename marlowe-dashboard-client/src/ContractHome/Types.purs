module ContractHome.Types
  ( State
  , ContractStatus(..)
  , PartitionedContracts
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Contract.Types (State) as Contract
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Marlowe.PAB (PlutusAppId)

type State
  = { status :: ContractStatus
    -- FIXME: We need to see if the performance hit of having to split the map between running
    --        and completed is worth not having state duplication (Two arrays and a Map). Also,
    --        we should check if this data belongs here or in Play.State.
    , contracts :: Map PlutusAppId Contract.State
    , selectedContractIndex :: Maybe PlutusAppId
    }

data ContractStatus
  = Running
  | Completed

derive instance eqContractStatus :: Eq ContractStatus

type PartitionedContracts
  = { completed :: Array Contract.State, running :: Array Contract.State }

data Action
  = OpenTemplateLibraryCard
  | SelectView ContractStatus
  | OpenContract PlutusAppId

instance actionIsEvent :: IsEvent Action where
  toEvent OpenTemplateLibraryCard = Just $ defaultEvent "OpenTemplateLibraryCard"
  toEvent (SelectView _) = Just $ defaultEvent "SelectView"
  toEvent (OpenContract _) = Just $ defaultEvent "OpenContract"
