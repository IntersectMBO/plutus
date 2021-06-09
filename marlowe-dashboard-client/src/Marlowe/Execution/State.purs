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
  ) where

import Prelude
import Data.Array as Array
import Data.BigInteger (fromInt)
import Data.Lens (view, (^.))
import Data.List (List)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, fromMaybe')
import Data.Tuple.Nested ((/\))
import Marlowe.Execution.Types (State, NamedAction(..), PendingTimeouts)
import Marlowe.Semantics (Accounts, Action(..), Case(..), ChoiceId(..), Contract(..), Input, Party, ReduceResult(..), Slot(..), SlotInterval(..), Timeouts(..), Token, TransactionInput(..), TransactionOutput(..), _accounts, _boundValues, _minSlot, computeTransaction, emptyState, evalValue, makeEnvironment, reduceContractUntilQuiescent, timeouts)
import Marlowe.Semantics (State) as Marlowe

initExecution :: Slot -> Contract -> State
initExecution currentSlot contract =
  let
    marloweState = emptyState currentSlot

    previousStates = mempty
  in
    { currentState: { marloweState, contract }
    , previousStates
    , mPendingTimeouts: Nothing
    , mNextTimeout: nextTimeout contract
    }

nextState :: TransactionInput -> State -> State
nextState txInput { currentState, previousStates } =
  let
    { marloweState, contract } = currentState

    TransactionInput { interval: SlotInterval minSlot maxSlot } = txInput

    { txOutState, txOutContract } = case computeTransaction txInput marloweState contract of
      (TransactionOutput { txOutState, txOutContract }) -> { txOutState, txOutContract }
      -- We should not have contracts which cause errors in the dashboard so we will just ignore error cases for now
      -- FIXME: Change nextState to return an Either
      -- TODO: SCP-2088 We need to discuss how to display the warnings that computeTransaction may give
      (Error _) -> { txOutState: marloweState, txOutContract: contract }
  in
    { currentState:
        { marloweState: txOutState
        , contract: txOutContract
        }
    , previousStates: Array.snoc previousStates { txInput, marloweState }
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

timeoutState :: Slot -> State -> State
timeoutState currentSlot { currentState, previousStates, mPendingTimeouts, mNextTimeout } =
  let
    Slot slot = currentSlot

    env = makeEnvironment slot slot

    advanceAllTimeouts ::
      Maybe Slot ->
      Array Slot ->
      Marlowe.State ->
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
                , marloweState: state'
                , contract: contract'
                }
        }

    { timeouts, marloweState, contract } =
      fromMaybe'
        ( \_ ->
            { timeouts: [], marloweState: currentState.marloweState, contract: currentState.contract }
        )
        mPendingTimeouts

    advancedTimeouts = advanceAllTimeouts mNextTimeout timeouts marloweState contract
  in
    { currentState
    , previousStates
    , mPendingTimeouts: advancedTimeouts.mPendingTimeouts
    , mNextTimeout: advancedTimeouts.mNextTimeout
    }

------------------------------------------------------------
isClosed :: State -> Boolean
isClosed { currentState: { contract: Close } } = true

isClosed _ = false

getActionParticipant :: NamedAction -> Maybe Party
getActionParticipant (MakeDeposit _ party _ _) = Just party

getActionParticipant (MakeChoice (ChoiceId _ party) _ _) = Just party

getActionParticipant _ = Nothing

extractNamedActions :: Slot -> State -> Array NamedAction
extractNamedActions _ { mPendingTimeouts: Just { contract: Close } } = [ CloseContract ]

extractNamedActions currentSlot { mPendingTimeouts: Just { marloweState, contract } } = extractActionsFromContract currentSlot marloweState contract

extractNamedActions currentSlot { currentState: { marloweState, contract } } = extractActionsFromContract currentSlot marloweState contract

-- a When can only progress if it has timed out or has Cases
extractActionsFromContract :: Slot -> Marlowe.State -> Contract -> Array NamedAction
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

-- This function expands the balances inside the Marlowe.State to all participants and tokens, using zero if
-- the participant does not have balance for that token.
expandBalances :: Array Party -> Array Token -> Marlowe.State -> Accounts
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
