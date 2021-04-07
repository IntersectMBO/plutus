module Marlowe.Execution where

import Prelude
import Data.Array as Array
import Data.BigInteger (BigInteger, fromInt)
import Data.Lens (Lens', Traversal', _Just, traversed, view)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe')
import Data.Symbol (SProxy(..))
import Marlowe.Semantics (AccountId, Action(..), Bound, Case(..), ChoiceId(..), ChosenNum, Contract(..), Input, Observation, Party, Payment, ReduceResult(..), Slot(..), SlotInterval(..), State, Timeouts(..), Token, TransactionInput(..), TransactionOutput(..), ValueId, _boundValues, _minSlot, computeTransaction, emptyState, evalValue, makeEnvironment, reduceContractUntilQuiescent, timeouts)

-- This represents a previous step in the execution. The state property corresponds to the state before the
-- txInput was applied and it's saved as an early optimization to calculate the balances at each step.
type PreviousState
  = { txInput :: TransactionInput
    , state :: State
    }

-- This represents the timeouts that hasn't been applied to the contract. When a step of a contract has timeout
-- nothing happens until the next InputTransaction. This could be an IDeposit or IChoose for the continuation
-- contract, or an empty transaction to advance or even close the contract. We store a separate contract and state
-- than the "current" contract/state because this is the predicted state that we would be in if we applied an
-- empty transaction, and this allow us to extract the NamedActions that needs to be applied next.
-- Also, we store the timeouts as an Array because it is possible that multiple continuations have timeouted
-- before we advance the contract.
type PendingTimeouts
  = { timeouts :: Array Slot
    , contract :: Contract
    , state :: State
    }

type ExecutionState
  = { previous :: Array PreviousState
    , current ::
        { state :: State
        , contract :: Contract
        }
    , mPendingTimeouts :: Maybe PendingTimeouts
    , mNextTimeout :: Maybe Slot
    }

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

isClosed :: ExecutionState -> Boolean
isClosed { current: { contract: Close } } = true

isClosed _ = false

initExecution :: Slot -> Contract -> ExecutionState
initExecution currentSlot contract =
  let
    previous = mempty

    state = emptyState currentSlot
  in
    { previous
    , current:
        { state
        , contract
        }
    , mPendingTimeouts: Nothing
    , mNextTimeout: nextTimeout contract
    }

nextTimeout :: Contract -> Maybe Slot
nextTimeout = timeouts >>> \(Timeouts { minTime }) -> minTime

mkInterval :: Slot -> Contract -> SlotInterval
mkInterval currentSlot contract = case nextTimeout contract of
  Nothing -> SlotInterval currentSlot (currentSlot + (Slot $ fromInt 10))
  Just minTime
    -- FIXME: I think this will fail in the PAB... we may need to return a Maybe SlotInterval and
    -- show an error. But also, if you delay confirming the action it could also cause the same type
    -- of failure, so maybe there is no need. Check after initial PAB integration.
    | minTime < currentSlot -> SlotInterval currentSlot currentSlot
    | otherwise -> SlotInterval currentSlot (minTime - (Slot $ fromInt 1))

mkTx :: Slot -> Contract -> List Input -> TransactionInput
mkTx currentSlot contract inputs =
  let
    interval = mkInterval currentSlot contract
  in
    TransactionInput { interval, inputs }

-- FIXME: Change the order of the arguments to::  TransactionInput -> ExecutionState  -> ExecutionState
nextState :: ExecutionState -> TransactionInput -> ExecutionState
nextState { previous, current } txInput =
  let
    { state, contract } = current

    TransactionInput { interval: SlotInterval minSlot maxSlot } = txInput

    { txOutState, txOutContract } = case computeTransaction txInput state contract of
      (TransactionOutput { txOutState, txOutContract }) -> { txOutState, txOutContract }
      -- We should not have contracts which cause errors in the dashboard so we will just ignore error cases for now
      -- FIXME: Change nextState to return an Either
      -- TODO: SCP-2088 We need to discuss how to display the warnings that computeTransaction may give
      (Error _) -> { txOutState: state, txOutContract: contract }
  in
    { previous: Array.snoc previous { txInput, state }
    , current:
        { state: txOutState
        , contract: txOutContract
        }
    , mPendingTimeouts: Nothing
    , mNextTimeout: nextTimeout txOutContract
    }

timeoutState :: Slot -> ExecutionState -> ExecutionState
timeoutState currentSlot { current, previous, mPendingTimeouts, mNextTimeout } =
  let
    Slot slot = currentSlot

    env = makeEnvironment slot slot

    advanceAllTimeouts ::
      Maybe Slot ->
      Array Slot ->
      State ->
      Contract ->
      { mNextTimeout :: Maybe Slot, mPendingTimeouts :: Maybe PendingTimeouts }
    advanceAllTimeouts mNextTimeout' newTimeouts state' contract'
      | mNextTimeout' >= Just currentSlot =
        let
          { txOutState, txOutContract } = case reduceContractUntilQuiescent env state' contract' of
            -- TODO: SCP-2088 We need to discuss how to display the warnings that computeTransaction may give
            ContractQuiescent warnings payments txOutState txOutContract -> { txOutState, txOutContract }
            -- FIXME: Change timeoutState to return an Either
            RRAmbiguousSlotIntervalError -> { txOutState: state', txOutContract: contract' }

          newNextTimeout = nextTimeout txOutContract
        in
          advanceAllTimeouts newNextTimeout (Array.snoc newTimeouts currentSlot) txOutState txOutContract
      | otherwise =
        { mNextTimeout: mNextTimeout'
        , mPendingTimeouts:
            if newTimeouts == mempty then
              Nothing
            else
              Just
                { timeouts: newTimeouts
                , state: state'
                , contract: contract'
                }
        }

    { state, contract, timeouts } =
      fromMaybe'
        ( \_ ->
            { contract: current.contract, state: current.state, timeouts: [] }
        )
        mPendingTimeouts

    advancedTimeouts = advanceAllTimeouts mNextTimeout timeouts state contract
  in
    { previous
    , current
    , mPendingTimeouts: advancedTimeouts.mPendingTimeouts
    , mNextTimeout: advancedTimeouts.mNextTimeout
    }

-- Represents the possible buttons that can be displayed on a contract stage card
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

getActionParticipant :: NamedAction -> Maybe Party
getActionParticipant (MakeDeposit _ party _ _) = Just party

getActionParticipant (MakeChoice (ChoiceId _ party) _ _) = Just party

getActionParticipant _ = Nothing

-- a When can only progress if it has timed out or has Cases
extractActionsFromContract :: Slot -> State -> Contract -> Array NamedAction
extractActionsFromContract _ _ Close = mempty

extractActionsFromContract currentSlot state contract@(When cases timeout cont)
  -- in the case of a timeout we need to provide an Evaluate action to all users to "manually" progress the contract
  | currentSlot > timeout =
    let
      minSlot = view _minSlot state

      emptyTx = TransactionInput { interval: SlotInterval minSlot minSlot, inputs: mempty }

      outputs = case computeTransaction emptyTx state cont of
        TransactionOutput { txOutPayments, txOutState } ->
          let
            oldBindings = view _boundValues state

            newBindings = view _boundValues txOutState

            bindings = Map.difference newBindings oldBindings
          in
            { payments: Array.fromFoldable txOutPayments, bindings: bindings }
        _ -> mempty
    in
      -- FIXME: Currently we don't have a way to display Evaluate so this can be dangerous.
      --        This should not happen for the demo as we are storing pending timeouts with
      --        the latest contract that hasn't timeouted.
      [ Evaluate outputs ]
  -- if there are no cases then there is no action that any user can take to progress the contract
  | otherwise = cases <#> \(Case action _) -> toNamedAction action
    where
    toNamedAction (Deposit a p t v) =
      let
        SlotInterval (Slot minSlot) (Slot maxSlot) = mkInterval currentSlot contract

        env = makeEnvironment minSlot maxSlot

        amount = evalValue env state v
      in
        MakeDeposit a p t amount

    toNamedAction (Choice cid bounds) = MakeChoice cid bounds Nothing

    toNamedAction (Notify obs) = MakeNotify obs

-- In reality other situations should never occur as contracts always reduce to When or Close
-- however someone could in theory publish a contract that starts with another Contract constructor
-- and we would want to enable moving forward with Evaluate
extractActionsFromContract _ _ _ = [ Evaluate mempty ]

extractNamedActions :: Slot -> ExecutionState -> Array NamedAction
extractNamedActions _ { mPendingTimeouts: Just { contract: Close } } = [ CloseContract ]

extractNamedActions currentSlot { mPendingTimeouts: Just { contract, state } } = extractActionsFromContract currentSlot state contract

extractNamedActions currentSlot { current: { state, contract } } = extractActionsFromContract currentSlot state contract
