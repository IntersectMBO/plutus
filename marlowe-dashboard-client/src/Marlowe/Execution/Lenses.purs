module Marlowe.Execution.Lenses
  ( _previousExecutionStates
  , _currentExecutionState
  , _mPendingTimeouts
  , _mNextTimeout
  , _state
  , _contract
  , _payments
  , _previousTransactions
  , _currentState
  , _currentContract
  , _currentPayments
  , _pendingTimeouts
  ) where

import Prelude
import Data.Lens (Lens', Traversal', _Just, traversed)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Marlowe.Execution.Types (CurrentExecutionState, ExecutionState, PendingTimeouts, PreviousExecutionState)
import Marlowe.Semantics (Contract, Payment, Slot, State, TransactionInput)

_previousExecutionStates :: Lens' ExecutionState (Array PreviousExecutionState)
_previousExecutionStates = prop (SProxy :: SProxy "previousExecutionStates")

_currentExecutionState :: Lens' ExecutionState (CurrentExecutionState)
_currentExecutionState = prop (SProxy :: SProxy "currentExecutionState")

_mPendingTimeouts :: Lens' ExecutionState (Maybe PendingTimeouts)
_mPendingTimeouts = prop (SProxy :: SProxy "mPendingTimeouts")

_mNextTimeout :: Lens' ExecutionState (Maybe Slot)
_mNextTimeout = prop (SProxy :: SProxy "mNextTimeout")

----------
_state :: forall a. Lens' { state :: State | a } State
_state = prop (SProxy :: SProxy "state")

_contract :: forall a. Lens' { contract :: Contract | a } Contract
_contract = prop (SProxy :: SProxy "contract")

_payments :: forall a. Lens' { payments :: List Payment | a } (List Payment)
_payments = prop (SProxy :: SProxy "payments")

_previousTransactions :: Traversal' ExecutionState TransactionInput
_previousTransactions = _previousExecutionStates <<< traversed <<< prop (SProxy :: SProxy "txInput")

_currentState :: Lens' ExecutionState State
_currentState = _currentExecutionState <<< _state

_currentContract :: Lens' ExecutionState Contract
_currentContract = _currentExecutionState <<< _contract

_currentPayments :: Lens' ExecutionState (List Payment)
_currentPayments = _currentExecutionState <<< _payments

_pendingTimeouts :: Traversal' ExecutionState (Array Slot)
_pendingTimeouts = prop (SProxy :: SProxy "mPendingTimeouts") <<< _Just <<< prop (SProxy :: SProxy "timeouts")
