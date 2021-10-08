module Marlowe.Execution.State
  ( mkInitialState
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

import Prologue
import Data.Array as Array
import Data.BigInteger (fromInt)
import Data.Lens (view, (^.))
import Data.List (List(..), concat, fromFoldable)
import Data.Map as Map
import Data.Maybe (fromMaybe, fromMaybe')
import Data.Tuple.Nested ((/\))
import Marlowe.Execution.Lenses (_resultingPayments)
import Marlowe.Execution.Types (NamedAction(..), PastAction(..), PendingTimeouts, State, TimeoutInfo)
import Marlowe.Semantics (Accounts, Action(..), Case(..), ChoiceId(..), Contract(..), Input, Party, Payment, ReduceResult(..), Slot(..), SlotInterval(..), Timeouts(..), Token, TransactionInput(..), TransactionOutput(..), _accounts, computeTransaction, emptyState, evalValue, makeEnvironment, reduceContractUntilQuiescent, timeouts)
import Marlowe.Semantics (State) as Semantic

mkInitialState :: Slot -> Contract -> State
mkInitialState currentSlot contract =
  { semanticState: emptyState currentSlot
  , contract
  , history: mempty
  , mPendingTimeouts: Nothing
  , mNextTimeout: nextTimeout contract
  }

nextState :: TransactionInput -> State -> State
nextState txInput { semanticState, contract, history } =
  let
    TransactionInput { interval: SlotInterval minSlot maxSlot, inputs } = txInput

    { txOutState, txOutContract, txOutPayments } = case computeTransaction txInput semanticState contract of
      (TransactionOutput { txOutState, txOutContract, txOutPayments }) -> { txOutState, txOutContract, txOutPayments }
      -- We should not have contracts which cause errors in the dashboard so we will just ignore error cases for now
      -- FIXME: Change nextState to return an Either
      -- TODO: SCP-2088 We need to discuss how to display the warnings that computeTransaction may give
      (Error _) -> { txOutState: semanticState, txOutContract: contract, txOutPayments: mempty }

    -- For the moment the only way to get an empty transaction is if there was a timeout,
    -- but later on there could be other reasons to move a contract forward, and we should
    -- compare with the contract to see the reason.
    action = case inputs of
      Nil -> TimeoutAction { slot: minSlot, missedActions: extractActionsFromContract minSlot semanticState contract }
      _ -> InputAction

    pastState =
      { balancesAtStart: semanticState ^. _accounts
      , action
      , txInput
      , balancesAtEnd: txOutState ^. _accounts
      , resultingPayments: txOutPayments
      }
  in
    { semanticState: txOutState
    , contract: txOutContract
    , history: Array.snoc history pastState
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

-- This function checks if the are any new timeouts in the current execution state
timeoutState :: Slot -> State -> State
timeoutState currentSlot { semanticState, contract, history, mPendingTimeouts, mNextTimeout } =
  let
    -- We start of by getting a PendingTimeout structure from the execution state (because the
    -- contract could already have some timeouts that were "advanced")
    { continuation, timeouts } =
      fromMaybe'
        ( \_ ->
            { continuation: { state: semanticState, contract }, timeouts: [] }
        )
        mPendingTimeouts

    -- This helper function does all the leg work.
    -- A contract step can be stale/timeouted but it does not advance on its own, it needs
    -- an empty transaction or the next meaningfull transaction. With this function we check if
    -- the contract has timeouted and calculate what would be the resulting continuation contract
    -- and resulting state if we'd apply an empty transaction.
    advanceAllTimeouts ::
      Maybe Slot ->
      Array TimeoutInfo ->
      Semantic.State ->
      Contract ->
      { mNextTimeout :: Maybe Slot, mPendingTimeouts :: Maybe PendingTimeouts }
    advanceAllTimeouts (Just timeoutSlot) newTimeouts state' contract'
      | timeoutSlot <= currentSlot =
        let
          Slot slot = currentSlot

          env = makeEnvironment slot slot

          { txOutState, txOutContract } = case reduceContractUntilQuiescent env state' contract' of
            -- TODO: SCP-2088 We need to discuss how to display the warnings that computeTransaction may give
            ContractQuiescent _ _ _ txOutState txOutContract -> { txOutState, txOutContract }
            -- FIXME: Change timeoutState to return an Either
            RRAmbiguousSlotIntervalError -> { txOutState: state', txOutContract: contract' }

          timeoutInfo =
            { slot: timeoutSlot
            , missedActions: extractActionsFromContract timeoutSlot state' contract'
            }

          newNextTimeout = nextTimeout txOutContract
        in
          advanceAllTimeouts newNextTimeout (Array.snoc newTimeouts timeoutInfo) txOutState txOutContract

    advanceAllTimeouts mNextTimeout' newTimeouts state' contract' =
      { mNextTimeout: mNextTimeout'
      , mPendingTimeouts:
          if newTimeouts == mempty then
            Nothing
          else
            Just
              { continuation: { state: state', contract: contract' }
              , timeouts: newTimeouts
              }
      }

    advancedTimeouts = advanceAllTimeouts mNextTimeout timeouts continuation.state continuation.contract
  in
    { semanticState
    , contract
    , history
    , mPendingTimeouts: advancedTimeouts.mPendingTimeouts
    , mNextTimeout: advancedTimeouts.mNextTimeout
    }

------------------------------------------------------------
isClosed :: State -> Boolean
isClosed { contract: Close } = true

isClosed _ = false

getActionParticipant :: NamedAction -> Maybe Party
getActionParticipant (MakeDeposit _ party _ _) = Just party

getActionParticipant (MakeChoice (ChoiceId _ party) _ _) = Just party

getActionParticipant _ = Nothing

extractNamedActions :: Slot -> State -> Array NamedAction
extractNamedActions _ { mPendingTimeouts: Just { continuation: { contract: Close } } } = [ CloseContract ]

extractNamedActions currentSlot { mPendingTimeouts: Just { continuation } } = extractActionsFromContract currentSlot continuation.state continuation.contract

extractNamedActions currentSlot { semanticState, contract } = extractActionsFromContract currentSlot semanticState contract

-- a When can only progress if it has timed out or has Cases
extractActionsFromContract :: Slot -> Semantic.State -> Contract -> Array NamedAction
extractActionsFromContract _ _ Close = mempty

extractActionsFromContract currentSlot semanticState contract@(When cases timeout cont) = cases <#> \(Case action _) -> toNamedAction action
  where
  toNamedAction (Deposit a p t v) =
    let
      SlotInterval (Slot minSlot) (Slot maxSlot) = mkInterval currentSlot contract

      env = makeEnvironment minSlot maxSlot

      amount = evalValue env semanticState v
    in
      MakeDeposit a p t amount

  toNamedAction (Choice cid bounds) = MakeChoice cid bounds Nothing

  toNamedAction (Notify obs) = MakeNotify obs

-- In reality other situations should never occur as contracts always reduce to When or Close
-- however someone could in theory publish a contract that starts with another Contract constructor
-- and we would want to enable moving forward with Evaluate
extractActionsFromContract _ _ _ = [ Evaluate mempty ]

-- This function expands the balances inside the Semantic.State to all participants and tokens,
-- using zero if the participant does not have balance for that token.
expandBalances :: Array Party -> Array Token -> Accounts -> Accounts
expandBalances participants tokens stateAccounts =
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
    -- FIXME: We should change this for a Maybe SlotInterval and return Nothing in this case.
    --        86400 is one day in seconds
    | minTime < currentSlot -> SlotInterval currentSlot (currentSlot + (Slot $ fromInt 86400))
    | otherwise -> SlotInterval currentSlot (minTime - (Slot $ fromInt 1))

getAllPayments :: State -> List Payment
getAllPayments { history } = concat $ fromFoldable $ map (view _resultingPayments) history
