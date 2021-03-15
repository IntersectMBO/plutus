module Marlowe.Execution where

import Prelude
import Data.Array (fromFoldable)
import Data.BigInteger (BigInteger, fromInt)
import Data.Lens (Lens', has, only, to, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Ord (greaterThanOrEq)
import Data.Symbol (SProxy(..))
import Marlowe.Semantics (AccountId, Action(..), Bound, Case(..), ChoiceId(..), ChosenNum, Contract(..), Input, Observation, Party, Payment, Slot(..), SlotInterval(..), State, Timeout, Token, TransactionInput(..), TransactionOutput(..), ValueId, _boundValues, _minSlot, computeTransaction, emptyState, evalValue, makeEnvironment)

-- Represents a historical step in a contract's life and is what you see on a Step card that is in the past,
-- that is the State as it was before it was executed and the TransactionInput that was applied.
-- We don't bother storing the Contract because it is not needed for displaying a hostorical card but this means
-- we need to store if the step timed out. This is all (possibly premature) optimization to avoid storing the
-- contract many times as it could be quite large
type ExecutionStep
  = { txInput :: TransactionInput
    , state :: State
    , timedOut :: Boolean
    }

type ExecutionState
  = { steps :: Array ExecutionStep
    , state :: State
    , contract :: Contract
    , namedActions :: Array NamedAction
    }

-- | Merge ExecutionStates preferring the left over the right
-- | steps are appended left to right and everything else is
-- | replaced with the left side values
merge :: ExecutionState -> ExecutionState -> ExecutionState
merge a b =
  { steps: a.steps <> b.steps
  , state: a.state
  , contract: a.contract
  , namedActions: a.namedActions
  }

_state :: Lens' ExecutionState State
_state = prop (SProxy :: SProxy "state")

_contract :: Lens' ExecutionState Contract
_contract = prop (SProxy :: SProxy "contract")

_namedActions :: Lens' ExecutionState (Array NamedAction)
_namedActions = prop (SProxy :: SProxy "namedActions")

initExecution :: Slot -> Contract -> ExecutionState
initExecution currentSlot contract =
  let
    steps = mempty

    state = emptyState currentSlot

    namedActions = extractNamedActions state contract
  in
    { steps, state, contract, namedActions }

hasTimeout :: Contract -> Maybe Timeout
hasTimeout (When _ t _) = Just t

hasTimeout _ = Nothing

mkTx :: ExecutionState -> List Input -> TransactionInput
mkTx { state } inputs =
  let
    currentSlot = view _minSlot state

    interval = SlotInterval currentSlot (currentSlot + Slot (fromInt 100)) -- FIXME: should this be minSlot minSlot? We need to think about ambiguous slot error
  in
    TransactionInput { interval, inputs }

-- Evaluate a Contract based on a State and a TransactionInput and return the new ExecutionState, having added a new ExecutinStep
nextState :: ExecutionState -> TransactionInput -> ExecutionState
nextState { steps, state, contract } txInput =
  let
    currentSlot = view _minSlot state

    { txOutState, txOutContract } = case computeTransaction txInput state contract of
      (TransactionOutput { txOutState, txOutContract }) -> { txOutState, txOutContract }
      -- We should not have contracts which cause errors in the dashboard so we will just ignore error cases for now
      (Error _) -> { txOutState: state, txOutContract: contract }

    namedActions = extractNamedActions txOutState txOutContract

    timedOut = case hasTimeout contract of
      Just t -> t < currentSlot
      _ -> false
  in
    { steps: [ { txInput, state, timedOut } ] <> steps
    , state: txOutState
    , contract: txOutContract
    , namedActions
    }

-- Represents the possible buttons that can be displayed on a contract stage card
data NamedAction
  -- Equivalent to Semantics.Action(Deposit)
  -- Creates IDeposit
  = MakeDeposit AccountId Party Token BigInteger
  -- Equivalent to Semantics.Action(Choice) but has ChosenNum since it is a stateful element that stores the users choice
  -- Creates IChoice
  -- FIXME: Why does this option have a ChosenNum? Shouldn't that be in the transaction?
  | MakeChoice ChoiceId (Array Bound) ChosenNum
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

getActionParticipant :: NamedAction -> Maybe Party
getActionParticipant (MakeDeposit _ party _ _) = Just party

getActionParticipant (MakeChoice (ChoiceId _ party) _ _) = Just party

getActionParticipant _ = Nothing

extractNamedActions :: State -> Contract -> Array NamedAction
extractNamedActions _ Close = mempty

-- FIXME We need to provide the current slot instead of minSlot
-- a When can only progress if it has timed out or has Cases
extractNamedActions state (When cases timeout cont)
  -- in the case of a timeout we need to provide an Evaluate action to all users to "manually" progress the contract
  | has (_minSlot <<< to (greaterThanOrEq timeout) <<< only true) state =
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
      [ Evaluate outputs ]
  -- if there are no cases then there is no action that any user can take to progress the contract
  | otherwise = cases <#> \(Case action _) -> toNamedAction action
    where
    toNamedAction (Deposit a p t v) =
      let
        minSlot = view (_minSlot <<< _Newtype) state

        env = makeEnvironment minSlot minSlot

        amount = evalValue env state v
      in
        MakeDeposit a p t amount

    toNamedAction (Choice cid bounds) = MakeChoice cid bounds zero

    toNamedAction (Notify obs) = MakeNotify obs

-- In reality other situations should never occur as contracts always reduce to When or Close
-- however someone could in theory publish a contract that starts with another Contract constructor
-- and we would want to enable moving forward with Evaluate
extractNamedActions _ _ = [ Evaluate mempty ]
