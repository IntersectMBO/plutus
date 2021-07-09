module Marlowe.Execution.Lenses
  ( _semanticState
  , _contract
  , _history
  , _previousTransactions
  , _mPendingTimeouts
  , _pendingTimeouts
  , _mNextTimeout
  , _initialSemanticState
  , _txInput
  , _resultingPayments
  , _nextSemanticState
  , _continuationContract
  , _timeouts
  ) where

import Prelude
import Data.Lens (Lens', Traversal', _Just, traversed)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Marlowe.Execution.Types (PastState, PendingTimeouts, State)
import Marlowe.Semantics (Contract, Payment, Slot, TransactionInput)
import Marlowe.Semantics (State) as Semantic

_semanticState :: Lens' State Semantic.State
_semanticState = prop (SProxy :: SProxy "semanticState")

_contract :: Lens' State Contract
_contract = prop (SProxy :: SProxy "contract")

_history :: Lens' State (Array PastState)
_history = prop (SProxy :: SProxy "history")

_previousTransactions :: Traversal' State TransactionInput
_previousTransactions = _history <<< traversed <<< _txInput

_mPendingTimeouts :: Lens' State (Maybe PendingTimeouts)
_mPendingTimeouts = prop (SProxy :: SProxy "mPendingTimeouts")

_pendingTimeouts :: Traversal' State (Array Slot)
_pendingTimeouts = _mPendingTimeouts <<< _Just <<< _timeouts

_mNextTimeout :: Lens' State (Maybe Slot)
_mNextTimeout = prop (SProxy :: SProxy "mNextTimeout")

----------
_initialSemanticState :: Lens' PastState Semantic.State
_initialSemanticState = prop (SProxy :: SProxy "initialSemanticState")

_txInput :: Lens' PastState TransactionInput
_txInput = prop (SProxy :: SProxy "txInput")

_resultingPayments :: Lens' PastState (List Payment)
_resultingPayments = prop (SProxy :: SProxy "resultingPayments")

----------
_nextSemanticState :: Lens' PendingTimeouts Semantic.State
_nextSemanticState = prop (SProxy :: SProxy "nextSemanticState")

_continuationContract :: Lens' PendingTimeouts Contract
_continuationContract = prop (SProxy :: SProxy "continuationContract")

_timeouts :: Lens' PendingTimeouts (Array Slot)
_timeouts = prop (SProxy :: SProxy "timeouts")
