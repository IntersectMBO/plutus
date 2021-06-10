module Marlowe.Execution.Lenses
  ( _previousState
  , _previousTransactions
  , _currentState
  , _currentContract
  , _mNextTimeout
  , _pendingTimeouts
  ) where

import Prelude
import Data.Lens (Lens', Traversal', _Just, traversed)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Marlowe.Execution.Types (ExecutionState, PreviousState)
import Marlowe.Semantics (Contract, Slot, State, TransactionInput)

_previousState :: Lens' ExecutionState (Array PreviousState)
_previousState = prop (SProxy :: SProxy "previous")

_previousTransactions :: Traversal' ExecutionState TransactionInput
_previousTransactions = prop (SProxy :: SProxy "previous") <<< traversed <<< prop (SProxy :: SProxy "txInput")

_currentState :: Lens' ExecutionState State
_currentState = prop (SProxy :: SProxy "current") <<< prop (SProxy :: SProxy "state")

_currentContract :: Lens' ExecutionState Contract
_currentContract = prop (SProxy :: SProxy "current") <<< prop (SProxy :: SProxy "contract")

_mNextTimeout :: Lens' ExecutionState (Maybe Slot)
_mNextTimeout = prop (SProxy :: SProxy "mNextTimeout")

_pendingTimeouts :: Traversal' ExecutionState (Array Slot)
_pendingTimeouts = prop (SProxy :: SProxy "mPendingTimeouts") <<< _Just <<< prop (SProxy :: SProxy "timeouts")
