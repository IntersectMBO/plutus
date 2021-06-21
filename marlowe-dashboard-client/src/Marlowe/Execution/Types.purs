module Marlowe.Execution.Types
  ( ExecutionState
  , PreviousExecutionState
  , CurrentExecutionState
  , PendingTimeouts
  , NamedAction(..)
  ) where

import Prelude
import Data.BigInteger (BigInteger)
import Data.List (List)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Marlowe.Semantics (AccountId, Bound, ChoiceId, ChosenNum, Contract, Observation, Party, Payment, Slot, State, Token, TransactionInput, ValueId)

type ExecutionState
  = { previousExecutionStates :: Array PreviousExecutionState
    , currentExecutionState :: CurrentExecutionState
    , mPendingTimeouts :: Maybe PendingTimeouts
    , mNextTimeout :: Maybe Slot
    }

-- The current execution state is either the initial state of the contract, or a function of the
-- last element in the `previous` array. It is saved as an early optimisation so that we don't need
-- to recalculate payments and account balances all the the time.
type CurrentExecutionState
  = { contract :: Contract
    , state :: State
    , payments :: List Payment
    }

-- Similar to the current execution state, the first three properties of the previous execution
-- state either represent the initial state of the contract, or are a function of the previous 
-- element in the `previous` array. The final property is the transaction input that was applied at
-- that step. In other words, apply the transaction input to the contract and state here, and you
-- get the *next* contract, state, and payments. The only thing we *need* to keep around,
-- therefore, is the transaction input - but we remember the rest to save having to calculate it
-- multiple times.
-- Note: the contract and state here represent the contract and state *before* the transaction
-- input is applied. Likewise, the payments are the payments made as a result of the *previous*
-- transaction input.
type PreviousExecutionState
  = { contract :: Contract
    , state :: State
    , payments :: List Payment
    , txInput :: TransactionInput
    }

-- This represents the timeouts that haven't been applied to the contract. When a step of a
-- contract has timedout, nothing happens until the next transaction input. This could be an
-- IDeposit or IChoose for the continuation contract, or an empty transaction to advance or even
-- close the contract. We store a separate contract and state than the "current" contract/state
-- because this is the predicted state that we would be in if we applied an empty transaction, and
-- this allows us to extract the NamedActions that need to be applied next. Also, we store the
-- timeouts as an Array because it is possible that multiple continuations have timedout before we
-- advance the contract.
type PendingTimeouts
  = { timeouts :: Array Slot
    , contract :: Contract
    , state :: State
    }

-- Represents the possible buttons that can be displayed on a contract step card
data NamedAction
  -- Equivalent to Semantics.Action(Deposit)
  -- Creates IDeposit
  = MakeDeposit AccountId Party Token BigInteger
  -- Equivalent to Semantics.Action(Choice) but has ChosenNum since it is a stateful element that
  -- stores the users choice
  -- Creates IChoice
  | MakeChoice ChoiceId (Array Bound) (Maybe ChosenNum)
  -- Equivalent to Semantics.Action(Notify) (can be applied by any user)
  -- Creates INotify
  | MakeNotify Observation
  -- An empty transaction needs to be submitted in order to trigger a change in the contract and
  -- we work out the details of what will happen when this occurs, currently we are interested in
  -- any payments that will be made and new bindings that will be evaluated
  -- Creates empty tx
  | Evaluate { payments :: Array Payment, bindings :: Map ValueId BigInteger }
  -- A special case of Evaluate where the only way the Contract can progress is to apply an empty
  -- transaction which results in the contract being closed
  -- Creates empty tx
  | CloseContract

derive instance eqNamedAction :: Eq NamedAction
