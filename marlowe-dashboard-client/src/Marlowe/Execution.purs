module Marlowe.Execution where

import Prelude
import Data.Array (fromFoldable)
import Data.BigInteger (BigInteger, fromInt)
import Data.Lens (Lens', view)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Marlowe.Semantics (AccountId, Action(..), Bound, Case(..), ChoiceId(..), ChosenNum, Contract(..), Input, Observation, Party, Payment, Slot(..), SlotInterval(..), State, Timeout, Timeouts(..), Token, TransactionInput(..), TransactionOutput(..), ValueId, _boundValues, _minSlot, computeTransaction, emptyState, evalValue, makeEnvironment, timeouts)

-- Represents a historical step in a contract's life.
data ExecutionStep
  = TransactionStep
    { txInput :: TransactionInput
    -- This is the state before the txInput was executed
    , state :: State
    }
  | TimeoutStep
    { timeoutSlot :: Slot
    -- This is the state the step had at the begining (before it timed-out)
    , state :: State
    }

type ExecutionState
  = { steps :: Array ExecutionStep
    , state :: State
    , contract :: Contract
    }

_state :: Lens' ExecutionState State
_state = prop (SProxy :: SProxy "state")

_contract :: Lens' ExecutionState Contract
_contract = prop (SProxy :: SProxy "contract")

_steps :: Lens' ExecutionState (Array ExecutionStep)
_steps = prop (SProxy :: SProxy "steps")

initExecution :: Slot -> Contract -> ExecutionState
initExecution currentSlot contract =
  let
    steps = mempty

    state = emptyState currentSlot
  in
    { steps, state, contract }

-- FIXME: probably remove, nextTimeout does the same using Semantic code.
hasTimeout :: Contract -> Maybe Timeout
hasTimeout (When _ t _) = Just t

hasTimeout _ = Nothing

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

-- Evaluate a Contract based on a State and a TransactionInput and return the new ExecutionState, having added a new ExecutinStep
nextState :: ExecutionState -> TransactionInput -> ExecutionState
nextState { steps, state, contract } txInput =
  let
    TransactionInput { interval: SlotInterval minSlot maxSlot } = txInput

    { txOutState, txOutContract } = case computeTransaction txInput state contract of
      (TransactionOutput { txOutState, txOutContract }) -> { txOutState, txOutContract }
      -- We should not have contracts which cause errors in the dashboard so we will just ignore error cases for now
      (Error _) -> { txOutState: state, txOutContract: contract }
  in
    { steps: steps <> [ TransactionStep { txInput, state } ]
    , state: txOutState
    , contract: txOutContract
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
  -- FIXME: probably add {payments:: Array } and add them to the close description
  | CloseContract

derive instance eqNamedAction :: Eq NamedAction

getActionParticipant :: NamedAction -> Maybe Party
getActionParticipant (MakeDeposit _ party _ _) = Just party

getActionParticipant (MakeChoice (ChoiceId _ party) _ _) = Just party

getActionParticipant _ = Nothing

extractNamedActions :: Slot -> State -> Contract -> Array NamedAction
extractNamedActions _ _ Close = mempty

-- a When can only progress if it has timed out or has Cases
extractNamedActions currentSlot state contract@(When cases timeout cont)
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
            { payments: fromFoldable txOutPayments, bindings: bindings }
        _ -> mempty
    in
      -- FIXME: Currently we don't have a way to display Evaluate so this can be dangerous.
      --        We talked with Alex that when a contract timeouts there doesn't need to be
      --        an explicity Evaluate, the next action will take care of that for us. If the
      --        continuation of a contract is a Close, then we need to extract the `CloseContract`
      --        so someone can pay to close the contract. If the continuation is a When, then we
      --        need to extract the actions as below. In any case, I think that instead of using
      --        `computeTransaction` and returning an Evaluate we should "advance" in the continuation
      --        and recursively call extractNamedActions.
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
extractNamedActions _ _ _ = [ Evaluate mempty ]
