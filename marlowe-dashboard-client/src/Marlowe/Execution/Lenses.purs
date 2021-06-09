module Marlowe.Execution.Lenses
  ( _currentState
  , _previousStates
  , _mPendingTimeouts
  , _mNextTimeout
  , _currentMarloweState
  , _currentContract
  , _previousTransactions
  , _pendingTimeouts
  ) where

import Prelude
import Data.Lens (Lens', Traversal', _Just, traversed)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Marlowe.Execution.Types (CurrentState, PreviousState, PendingTimeouts, State)
import Marlowe.Semantics (Contract, Slot, TransactionInput)
import Marlowe.Semantics (State) as Marlowe

_currentState :: Lens' State CurrentState
_currentState = prop (SProxy :: SProxy "currentState")

_previousStates :: Lens' State (Array PreviousState)
_previousStates = prop (SProxy :: SProxy "previousStates")

_mPendingTimeouts :: Lens' State (Maybe PendingTimeouts)
_mPendingTimeouts = prop (SProxy :: SProxy "mPendingTimeouts")

_mNextTimeout :: Lens' State (Maybe Slot)
_mNextTimeout = prop (SProxy :: SProxy "mNextTimeout")

------------------------------------------------------------
_currentMarloweState :: Lens' State Marlowe.State
_currentMarloweState = _currentState <<< prop (SProxy :: SProxy "marloweState")

_currentContract :: Lens' State Contract
_currentContract = _currentState <<< prop (SProxy :: SProxy "contract")

_previousTransactions :: Traversal' State TransactionInput
_previousTransactions = _previousStates <<< traversed <<< prop (SProxy :: SProxy "txInput")

_pendingTimeouts :: Traversal' State (Array Slot)
_pendingTimeouts = _mPendingTimeouts <<< _Just <<< prop (SProxy :: SProxy "timeouts")
