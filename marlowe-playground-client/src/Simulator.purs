module Simulator
  ( updateMarloweState
  , applyInput
  , hasHistory
  , updateStateP
  , updateContractInStateP
  , updatePossibleActions
  , inFuture
  , moveToSignificantSlot
  , moveToSlot
  , nextSignificantSlot
  ) where

import Prelude
import Control.Monad.State (class MonadState)
import Data.Array (fromFoldable, mapMaybe, sort, toUnfoldable, uncons)
import Data.Either (Either(..))
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Lens (has, modifying, nearly, over, previewOn, set, use, view, (^.))
import Data.List (List(..))
import Data.List as List
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap, wrap)
import Data.NonEmpty (foldl1, (:|))
import Data.NonEmptyList.Extra (extendWith)
import Data.NonEmptyList.Lens (_Tail)
import Data.Tuple (Tuple(..))
import Marlowe.Extended (toCore)
import Marlowe.Extended as EM
import Marlowe.Holes (fromTerm)
import Marlowe.Linter (lint)
import Marlowe.Linter as L
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (Action(..), Bound(..), ChoiceId(..), ChosenNum, Contract(..), Environment(..), Input, IntervalResult(..), Observation, Party, Slot, SlotInterval(..), State, Timeouts(..), TransactionError(..), TransactionInput(..), TransactionOutput(..), _minSlot, boundFrom, computeTransaction, emptyState, evalValue, extractRequiredActionsWithTxs, fixInterval, moneyInContract, timeouts)
import Marlowe.Semantics as S
import SimulationPage.Types (ActionInput(..), ActionInputId(..), ExecutionState(..), ExecutionStateRecord, MarloweEvent(..), MarloweState, Parties, _SimulationRunning, _contract, _currentMarloweState, _editorErrors, _executionState, _holes, _log, _marloweState, _moneyInContract, _moveToAction, _pendingInputs, _possibleActions, _slot, _state, _transactionError, _transactionWarnings, otherActionsParty)

minimumBound :: Array Bound -> ChosenNum
minimumBound bnds = case uncons (map boundFrom bnds) of
  Just { head, tail } -> foldl1 min (head :| tail)
  Nothing -> zero

actionToActionInput :: State -> Action -> Tuple ActionInputId ActionInput
actionToActionInput state (Deposit accountId party token value) =
  let
    minSlot = state ^. _minSlot

    evalResult = evalValue env state value

    env = Environment { slotInterval: (SlotInterval minSlot minSlot) }
  in
    Tuple (DepositInputId accountId party token evalResult) (DepositInput accountId party token evalResult)

actionToActionInput _ (Choice choiceId bounds) = Tuple (ChoiceInputId choiceId) (ChoiceInput choiceId bounds (minimumBound bounds))

actionToActionInput _ (Notify _) = Tuple NotifyInputId NotifyInput

combineChoices :: ActionInput -> ActionInput -> ActionInput
combineChoices (ChoiceInput choiceId1 bounds1 _) (ChoiceInput choiceId2 bounds2 _)
  | choiceId1 == choiceId2 = (ChoiceInput choiceId2 combinedBounds (minimumBound combinedBounds))
    where
    combinedBounds = bounds1 <> bounds2

combineChoices a1 a2 = a2

simplifyActionInput :: ActionInput -> ActionInput
simplifyActionInput (ChoiceInput choiceId bounds minBound) = ChoiceInput choiceId (simplifyBounds bounds) minBound

simplifyActionInput other = other

simplifyBounds :: Array Bound -> Array Bound
simplifyBounds bounds = fromFoldable (simplifyBoundList (toUnfoldable (sort bounds)))

simplifyBoundList :: List Bound -> List Bound
simplifyBoundList (Cons (Bound low1 high1) (Cons b2@(Bound low2 high2) rest))
  | high1 >= low2 = simplifyBoundList (Cons (Bound (min low1 low2) (max high1 high2)) rest)
  | otherwise = (Cons (Bound low1 high1) (simplifyBoundList (Cons b2 rest)))

simplifyBoundList l = l

-- TODO: This doesn't seem to be used, confirm and delete
getAsMuchStateAsPossible :: forall m t0. MonadState { marloweState :: NonEmptyList MarloweState | t0 } m => m State
getAsMuchStateAsPossible = do
  executionState <- use (_currentMarloweState <<< _executionState)
  pure
    ( case executionState of
        SimulationRunning runRecord -> runRecord.state
        SimulationNotStarted notRunRecord -> emptyState notRunRecord.initialSlot
    )

inFuture :: forall r. { marloweState :: NonEmptyList MarloweState | r } -> Slot -> Boolean
inFuture state slot = has (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _slot <<< nearly zero ((>) slot)) state

-- TODO: This seems to be used only on the Wallet module, which is not being used (and probably should)
--       be removed. Confirm and delete.
updateContractInStateP :: String -> MarloweState -> MarloweState
updateContractInStateP text state = case parseContract text of
  Right parsedContract ->
    let
      lintResult = lint Nil parsedContract

      mContract = fromTerm parsedContract
    in
      -- We reuse the extended Marlowe parser for now since it is a superset
      case mContract of
        Just extendedContract -> case toCore (extendedContract :: EM.Contract) of
          Just contract -> set _editorErrors [] $ set (_executionState <<< _SimulationRunning <<< _contract) contract state
          Nothing -> (set _holes mempty) state
        Nothing ->
          let
            holes = view L._holes lintResult
          in
            (set _holes holes) state
  Left error -> (set _holes mempty) state

updatePossibleActions :: MarloweState -> MarloweState
updatePossibleActions oldState@{ executionState: SimulationRunning executionState } =
  let
    contract = executionState ^. _contract

    state = executionState ^. _state

    currentSlot = executionState ^. _slot

    txInput = stateToTxInput executionState

    (Tuple nextState actions) = extractRequiredActionsWithTxs txInput state contract

    usefulActions = mapMaybe removeUseless actions

    slot = fromMaybe (add one currentSlot) (nextSignificantSlot oldState)

    rawActionInputs = Map.fromFoldableWith combineChoices $ map (actionToActionInput nextState) usefulActions

    actionInputs = map simplifyActionInput rawActionInputs

    moveTo = if contract == Close then Nothing else Just $ MoveToSlot slot

    newExecutionState =
      executionState
        # over _possibleActions (updateActions actionInputs)
        # set (_possibleActions <<< _moveToAction) moveTo
  in
    set _executionState (SimulationRunning newExecutionState) oldState
  where
  removeUseless :: Action -> Maybe Action
  removeUseless action@(Notify observation) = if evalObservation oldState observation then Just action else Nothing

  removeUseless action = Just action

  updateActions :: Map ActionInputId ActionInput -> Parties -> Parties
  updateActions actionInputs oldInputs = foldlWithIndex (addButPreserveActionInputs oldInputs) mempty actionInputs

  addButPreserveActionInputs :: Parties -> ActionInputId -> Parties -> ActionInput -> Parties
  addButPreserveActionInputs oldInputs actionInputIdx m actionInput =
    let
      party = actionPerson actionInput
    in
      wrap $ appendValue (unwrap m) (unwrap oldInputs) party actionInputIdx actionInput

  actionPerson :: ActionInput -> Party
  actionPerson (DepositInput _ party _ _) = party

  actionPerson (ChoiceInput (ChoiceId _ party) _ _) = party

  -- We have a special person for notifications
  actionPerson _ = otherActionsParty

  appendValue :: forall k k2 v2. Ord k => Ord k2 => Map k (Map k2 v2) -> Map k (Map k2 v2) -> k -> k2 -> v2 -> Map k (Map k2 v2)
  appendValue m oldMap k k2 v2 = Map.alter (alterMap k2 (findWithDefault2 v2 k k2 oldMap)) k m

  alterMap :: forall k v. Ord k => k -> v -> Maybe (Map k v) -> Maybe (Map k v)
  alterMap k v Nothing = Just $ Map.singleton k v

  alterMap k v (Just vs) = Just $ Map.insert k v vs

  findWithDefault2 :: forall k k2 v2. Ord k => Ord k2 => v2 -> k -> k2 -> Map k (Map k2 v2) -> v2
  findWithDefault2 def k k2 m = case Map.lookup k m of
    Just m2 -> case Map.lookup k2 m2 of
      Just v -> v
      Nothing -> def
    Nothing -> def

updatePossibleActions oldState = oldState

-- TODO: Probably rename to "applyPendingInputs"
updateStateP :: MarloweState -> MarloweState
updateStateP oldState@{ executionState: SimulationRunning executionState } = newState
  where
  txInput@(TransactionInput txIn) = stateToTxInput executionState

  newState = case computeTransaction txInput (executionState ^. _state) (executionState ^. _contract) of
    TransactionOutput { txOutWarnings, txOutPayments, txOutState, txOutContract } ->
      let
        newExecutionState =
          ( set _transactionError Nothing
              <<< set _transactionWarnings (fromFoldable txOutWarnings)
              <<< set _pendingInputs mempty
              <<< set _state txOutState
              <<< set _moneyInContract (moneyInContract txOutState)
              <<< over _log (append (fromFoldable (map (OutputEvent txIn.interval) txOutPayments)))
              <<< over _log (append [ InputEvent txInput ])
          )
            executionState
      in
        set _executionState (SimulationRunning (set _contract txOutContract newExecutionState)) oldState
    Error TEUselessTransaction -> oldState
    Error txError ->
      let
        newExecutionState =
          ( set _transactionError (Just txError)
              -- apart from setting the error, we also removing the pending inputs
              
              -- otherwise there can be hidden pending inputs in the simulation
              
              <<< set _pendingInputs mempty
          )
            executionState
      in
        set _executionState (SimulationRunning newExecutionState) oldState

updateStateP oldState = oldState

updateSlot :: Slot -> MarloweState -> MarloweState
updateSlot = set (_executionState <<< _SimulationRunning <<< _slot)

-- TODO: Probably rename to `pendingTransactionInputs`
stateToTxInput :: ExecutionStateRecord -> TransactionInput
stateToTxInput executionState =
  let
    slot = executionState ^. _slot

    interval = SlotInterval slot slot

    inputs = executionState ^. _pendingInputs
  in
    TransactionInput { interval: interval, inputs: (List.fromFoldable inputs) }

updateMarloweState ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  (MarloweState -> MarloweState) ->
  m Unit
updateMarloweState f = modifying _marloweState (extendWith (updatePossibleActions <<< f))

-- TODO: This doesn't seem to be used, confirm and delete
updateContractInState ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  String ->
  m Unit
updateContractInState contents = modifying _currentMarloweState (updatePossibleActions <<< updateContractInStateP contents)

-- TODO: This doesn't seem to be used, confirm and delete
applyTransactions ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  m Unit
applyTransactions = modifying _marloweState (extendWith (updatePossibleActions <<< updateStateP))

applyInput ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  (Array Input -> Array Input) ->
  m Unit
applyInput inputs = modifying _marloweState (extendWith (updatePossibleActions <<< updateStateP <<< (over (_executionState <<< _SimulationRunning <<< _pendingInputs) inputs)))

-- TODO: Join moveToSignificantSlot and moveToSlot. See note on SimulationPage.State::handleAction MoveSlot
moveToSignificantSlot ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  Slot ->
  m Unit
moveToSignificantSlot slot =
  modifying
    _marloweState
    ( extendWith
        ( updatePossibleActions
            <<< updateStateP
            <<< updateSlot slot
        )
    )

moveToSlot ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  Slot ->
  m Unit
moveToSlot slot =
  modifying
    _marloweState
    ( extendWith
        ( updatePossibleActions
            <<< updateSlot slot
        )
    )

hasHistory :: forall s. { marloweState :: NonEmptyList MarloweState | s } -> Boolean
hasHistory state = case state ^. (_marloweState <<< _Tail) of
  Nil -> false
  Cons _ _ -> true

evalObservation :: MarloweState -> Observation -> Boolean
evalObservation state@{ executionState: SimulationRunning executionState } observation =
  let
    txInput = stateToTxInput executionState
  in
    case fixInterval (unwrap txInput).interval (executionState ^. _state) of
      IntervalTrimmed env state' -> S.evalObservation env state' observation
      -- if there is an error in the state we will say that the observation is false.
      -- Nothing should happen anyway because applying the input will fail later
      IntervalError _ -> false

evalObservation state observation = false

-- TODO: Probably rename to `nextTimeout` to match the same function of Marlowe.Execution in
--       the dashboard
nextSignificantSlot :: MarloweState -> Maybe Slot
nextSignificantSlot state = do
  mContract <- previewOn state (_executionState <<< _SimulationRunning <<< _contract)
  let
    Timeouts { minTime } = timeouts mContract
  minTime
