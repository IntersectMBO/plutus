module Marlowe.Execution.Lenses
  ( _semanticState
  , _contract
  , _history
  , _previousTransactions
  , _mPendingTimeouts
  , _pendingTimeouts
  , _mNextTimeout
  , _balancesAtStart
  , _txInput
  , _balancesAtEnd
  , _resultingPayments
  , _continuationState
  , _continuationContract
  ) where

import Prologue
import Data.Lens (Lens', Traversal', _Just, traversed)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Symbol (SProxy(..))
import Marlowe.Execution.Types (ContractAndState, PastState, PendingTimeouts, State, TimeoutInfo)
import Marlowe.Semantics (Contract, Payment, Slot, TransactionInput, Accounts)
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

_pendingTimeouts :: Traversal' State (Array TimeoutInfo)
_pendingTimeouts = _mPendingTimeouts <<< _Just <<< _timeouts

_mNextTimeout :: Lens' State (Maybe Slot)
_mNextTimeout = prop (SProxy :: SProxy "mNextTimeout")

----------
_balancesAtStart :: Lens' PastState Accounts
_balancesAtStart = prop (SProxy :: SProxy "balancesAtStart")

_txInput :: Lens' PastState TransactionInput
_txInput = prop (SProxy :: SProxy "txInput")

_balancesAtEnd :: Lens' PastState Accounts
_balancesAtEnd = prop (SProxy :: SProxy "balancesAtEnd")

_resultingPayments :: Lens' PastState (List Payment)
_resultingPayments = prop (SProxy :: SProxy "resultingPayments")

----------
_continuation :: Lens' PendingTimeouts ContractAndState
_continuation = prop (SProxy :: SProxy "continuation")

_continuationState :: Lens' PendingTimeouts Semantic.State
_continuationState = _continuation <<< prop (SProxy :: SProxy "state")

_continuationContract :: Lens' PendingTimeouts Contract
_continuationContract = _continuation <<< prop (SProxy :: SProxy "contract")

_timeouts :: Lens' PendingTimeouts (Array TimeoutInfo)
_timeouts = prop (SProxy :: SProxy "timeouts")
