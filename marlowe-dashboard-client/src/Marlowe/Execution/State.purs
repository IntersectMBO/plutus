module Marlowe.Execution.State
  ( initExecution
  , nextState
  , nextTimeout
  , mkTx
  , timeoutState
  , isClosed
  , getActionParticipant
  , extractNamedActions
  , expandBalances
  , getAllPayments
  ) where

import Prelude
import Data.Array as Array
import Data.BigInteger (fromInt)
import Data.Lens (view, (^.))
import Data.List (List, concat, fromFoldable, snoc)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, fromMaybe')
import Data.Tuple.Nested ((/\))
import Marlowe.Execution.Lenses (_currentPayments, _payments)
import Marlowe.Execution.Types (ExecutionState, NamedAction(..), PendingTimeouts)
import Marlowe.Semantics (Accounts, Action(..), Case(..), ChoiceId(..), Contract(..), Input, Party, Payment, ReduceResult(..), Slot(..), SlotInterval(..), State, Timeouts(..), Token, TransactionInput(..), TransactionOutput(..), _accounts, _boundValues, _minSlot, computeTransaction, emptyState, evalValue, makeEnvironment, reduceContractUntilQuiescent, timeouts)

initExecution :: Slot -> Contract -> ExecutionState
initExecution currentSlot contract =
  { previousExecutionStates: mempty
  , currentExecutionState:
      { state: emptyState currentSlot
      , contract
      , payments: mempty
      }
  , mPendingTimeouts: Nothing
  , mNextTimeout: nextTimeout contract
  }

-- FIXME: Change the order of the arguments to::  TransactionInput -> ExecutionState  -> ExecutionState
nextState :: ExecutionState -> TransactionInput -> ExecutionState
nextState { previousExecutionStates, currentExecutionState } txInput =
  let
    { contract, state, payments } = currentExecutionState

    TransactionInput { interval: SlotInterval minSlot maxSlot } = txInput

    { txOutState, txOutContract, txOutPayments } = case computeTransaction txInput state contract of
      (TransactionOutput { txOutState, txOutContract, txOutPayments }) -> { txOutState, txOutContract, txOutPayments }
      -- We should not have contracts which cause errors in the dashboard so we will just ignore error cases for now
      -- FIXME: Change nextState to return an Either
      -- TODO: SCP-2088 We need to discuss how to display the warnings that computeTransaction may give
      (Error _) -> { txOutState: state, txOutContract: contract, txOutPayments: payments }
  in
    { previousExecutionStates: Array.snoc previousExecutionStates { contract, state, payments, txInput }
    , currentExecutionState:
        { contract: txOutContract
        , state: txOutState
        , payments: txOutPayments
        }
    , mPendingTimeouts: Nothing
    , mNextTimeout: nextTimeout txOutContract
    }

nextTimeout :: Contract -> Maybe Slot
nextTimeout = timeouts >>> \(Timeouts { minTime }) -> minTime

mkTx :: Slot -> Contract -> List Input -> TransactionInput
mkTx currentSlot contract inputs =
  let
    interval = mkInterval currentSlot contract
  in
    TransactionInput { interval, inputs }

timeoutState :: Slot -> ExecutionState -> ExecutionState
timeoutState currentSlot { previousExecutionStates, currentExecutionState, mPendingTimeouts, mNextTimeout } =
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
      | mNextTimeout' /= Nothing && mNextTimeout' <= Just currentSlot =
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

    { contract, state, timeouts } =
      fromMaybe'
        ( \_ ->
            { contract: currentExecutionState.contract, state: currentExecutionState.state, timeouts: [] }
        )
        mPendingTimeouts

    advancedTimeouts = advanceAllTimeouts mNextTimeout timeouts state contract
  in
    { previousExecutionStates
    , currentExecutionState
    , mPendingTimeouts: advancedTimeouts.mPendingTimeouts
    , mNextTimeout: advancedTimeouts.mNextTimeout
    }

------------------------------------------------------------
isClosed :: ExecutionState -> Boolean
isClosed { currentExecutionState: { contract: Close } } = true

isClosed _ = false

getActionParticipant :: NamedAction -> Maybe Party
getActionParticipant (MakeDeposit _ party _ _) = Just party

getActionParticipant (MakeChoice (ChoiceId _ party) _ _) = Just party

getActionParticipant _ = Nothing

extractNamedActions :: Slot -> ExecutionState -> Array NamedAction
extractNamedActions _ { mPendingTimeouts: Just { contract: Close } } = [ CloseContract ]

extractNamedActions currentSlot { mPendingTimeouts: Just { contract, state } } = extractActionsFromContract currentSlot state contract

extractNamedActions currentSlot { currentExecutionState: { contract, state } } = extractActionsFromContract currentSlot state contract

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

-- This function expands the balances inside the Semantic.State to all participants and tokens, using zero if the participant
-- does not have balance for that token.
expandBalances :: Array Party -> Array Token -> State -> Accounts
expandBalances participants tokens state =
  let
    stateAccounts = state ^. _accounts
  in
    Map.fromFoldable do
      party <- participants
      tokens
        <#> \token ->
            let
              key = party /\ token
            in
              key /\ (fromMaybe zero $ Map.lookup key stateAccounts)

mkInterval :: Slot -> Contract -> SlotInterval
mkInterval currentSlot contract = case nextTimeout contract of
  Nothing -> SlotInterval currentSlot (currentSlot + (Slot $ fromInt 10))
  Just minTime
    -- FIXME: I think this will fail in the PAB... we may need to return a Maybe SlotInterval and
    -- show an error. But also, if you delay confirming the action it could also cause the same type
    -- of failure, so maybe there is no need. Check after initial PAB integration.
    | minTime < currentSlot -> SlotInterval currentSlot currentSlot
    | otherwise -> SlotInterval currentSlot (minTime - (Slot $ fromInt 1))

getAllPayments :: ExecutionState -> List Payment
getAllPayments executionState@{ previousExecutionStates } =
  let
    previousPayments = fromFoldable $ map (view _payments) previousExecutionStates

    currentPayments = view _currentPayments executionState
  in
    concat $ snoc previousPayments currentPayments
