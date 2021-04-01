module ContractHome.Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Contract.Types (State) as Contract
import Data.Maybe (Maybe(..))
import Marlowe.Semantics (Slot(..))

data ContractStatus
  = Running
  | Completed

derive instance eqContractStatus :: Eq ContractStatus

type State
  = { status :: ContractStatus
    -- FIXME: We are currently using an Array for holding all the contracts and a
    --        Maybe Int for seeing which one is selected. Eventually, this would probably
    --        be a `Map ContractId Contract.State` and a `Maybe ContractId`. We need to see how
    --        we identify contracts between the FE and BE and also if the performance hit of having
    --        to split the map between running and completed is worth not having state duplication
    --        (Two arrays and a Map).
    --        Also, we should check if this data belongs here or in PlayState
    , contracts :: Array (Contract.State)
    , selectedContractIndex :: Maybe Int
    }

data Action
  = ToggleTemplateLibraryCard
  | SelectView ContractStatus
  | OpenContract Int
  | AdvanceTimeoutedContracts Slot

instance actionIsEvent :: IsEvent Action where
  toEvent ToggleTemplateLibraryCard = Just $ defaultEvent "ToggleTemplateLibraryCard"
  toEvent (SelectView _) = Just $ defaultEvent "SelectView"
  toEvent (OpenContract _) = Just $ defaultEvent "OpenContract"
  toEvent (AdvanceTimeoutedContracts _) = Nothing
