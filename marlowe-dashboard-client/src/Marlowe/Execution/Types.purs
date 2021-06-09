module Marlowe.Execution.Types
  ( State
  , CurrentState
  , PreviousState
  , PendingTimeouts
  , NamedAction(..)
  ) where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Marlowe.Semantics (AccountId, Bound, ChoiceId, ChosenNum, Contract, Observation, Party, Payment, Slot, Token, TransactionInput, ValueId)
import Marlowe.Semantics (State) as Marlowe

type State
  = { currentState :: CurrentState
    , previousStates :: Array PreviousState
    , mPendingTimeouts :: Maybe PendingTimeouts
    , mNextTimeout :: Maybe Slot
    }

type CurrentState
  = { marloweState :: Marlowe.State
    , contract :: Contract
    }

-- This represents a previous stage in the execution. The state property corresponds to the state before
-- the TransactionInput was applied and it's saved as an early optimization to calculate the balances at
-- each step.
type PreviousState
  = { marloweState :: Marlowe.State
    , txInput :: TransactionInput
    }

-- This represents the timeouts that haven't been applied to the contract. When a step of a contract has timedout
-- nothing happens until the next InputTransaction. This could be an IDeposit or IChoose for the continuation
-- contract, or an empty transaction to advance or even close the contract. We store a separate contract and
-- state than the "current" contract/state because this is the predicted state that we would be in if we applied
-- an empty transaction, and this allows us to extract the NamedActions that need to be applied next. Also, we
-- store the timeouts as an Array because it is possible that multiple continuations have timedout before we
-- advance the contract.
type PendingTimeouts
  = { timeouts :: Array Slot
    , marloweState :: Marlowe.State
    , contract :: Contract
    }

-- This represents the possible buttons that can be displayed on a contract stage card.
data NamedAction
  -- Equivalent to Semantics.Action(Deposit)
  -- Creates IDeposit
  = MakeDeposit AccountId Party Token BigInteger
  -- Equivalent to Semantics.Action(Choice) but has ChosenNum since it is a stateful element that stores the users choice
  -- Creates IChoice
  | MakeChoice ChoiceId (Array Bound) (Maybe ChosenNum)
  -- Equivalent to Semantics.Action(Notify) (can be applied by any user)
  -- Creates INotify
  | MakeNotify Observation
  -- An empty transaction needs to be submitted in order to trigger a change in the contract
  -- and we work out the details of what will happen when this occurs, currently we are interested
  -- in any payments that will be made and new bindings that will be evaluated
  -- Creates empty tx
  | Evaluate { payments :: Array Payment, bindings :: Map ValueId BigInteger }
  -- A special case of Evaluate where the only way the Contract can progress is to apply an empty
  -- transaction which results in the contract being closed
  -- Creates empty tx
  | CloseContract

derive instance eqNamedAction :: Eq NamedAction
