module Simulator.State
  ( applyInput
  , applyTransactions
  , updateMarloweState
  , hasHistory
  , applyPendingInputs
  , updatePossibleActions
  , inFuture
  , moveToSlot
  , emptyExecutionStateWithSlot
  , emptyMarloweState
  , mapPartiesActionInput
  ) where

import Prelude
import Control.Monad.State (class MonadState)
import Data.Array (fromFoldable, mapMaybe, sort, toUnfoldable, uncons)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Lens (has, modifying, nearly, over, previewOn, set, to, use, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.List (List(..))
import Data.List as List
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (unwrap, wrap)
import Data.NonEmpty (foldl1, (:|))
import Data.NonEmptyList.Extra (extendWith)
import Data.NonEmptyList.Lens (_Tail)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Marlowe.Holes (Contract(..), Term(..), TransactionOutput(..), computeTransaction, fromTerm, reduceContractUntilQuiescent)
import Marlowe.Holes as T
import Marlowe.Semantics (Action(..), Bound(..), ChoiceId(..), ChosenNum, Environment(..), Input, IntervalResult(..), Observation, Party, Slot, SlotInterval(..), State, Timeouts(..), TransactionError(..), TransactionInput(..), _minSlot, boundFrom, emptyState, evalValue, fixInterval, moneyInContract, timeouts)
import Marlowe.Semantics as S
import Marlowe.Template (getPlaceholderIds, initializeTemplateContent)
import Simulator.Lenses (_SimulationRunning, _contract, _currentMarloweState, _executionState, _log, _marloweState, _moneyInContract, _moveToAction, _pendingInputs, _possibleActions, _slot, _state, _transactionError, _transactionWarnings)
import Simulator.Types (ActionInput(..), ActionInputId(..), ExecutionState(..), ExecutionStateRecord, MarloweEvent(..), MarloweState, Parties(..), otherActionsParty)

emptyExecutionStateWithSlot :: Slot -> Term T.Contract -> ExecutionState
emptyExecutionStateWithSlot sn cont =
  SimulationRunning
    { possibleActions: mempty
    , pendingInputs: mempty
    , transactionError: Nothing
    , transactionWarnings: mempty
    , log: mempty
    , state: emptyState sn
    , slot: sn
    , moneyInContract: mempty
    , contract: cont
    }

simulationNotStartedWithSlot :: Slot -> Maybe (Term T.Contract) -> ExecutionState
simulationNotStartedWithSlot slot mContract =
  SimulationNotStarted
    { initialSlot: slot
    , termContract: mContract
    -- FIXME: check if I should implement Template for Term or if this is fine.
    -- , templateContent: maybe mempty (initializeTemplateContent <<< getPlaceholderIds) mContract
    , templateContent: maybe mempty (initializeTemplateContent <<< getPlaceholderIds) mContract
    }

simulationNotStarted :: Maybe (Term T.Contract) -> ExecutionState
simulationNotStarted = simulationNotStartedWithSlot zero

emptyMarloweState :: Maybe (Term T.Contract) -> MarloweState
emptyMarloweState mContract =
  { editorErrors: mempty
  , editorWarnings: mempty
  , holes: mempty
  , executionState: simulationNotStarted mContract
  }

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

inFuture :: forall r. { marloweState :: NonEmptyList MarloweState | r } -> Slot -> Boolean
inFuture state slot = has (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _slot <<< nearly zero ((>) slot)) state

updatePossibleActions :: MarloweState -> MarloweState
updatePossibleActions oldState@{ executionState: SimulationRunning executionState } =
  let
    contract = executionState ^. _contract

    state = executionState ^. _state

    currentSlot = executionState ^. _slot

    txInput = pendingTransactionInputs executionState

    (Tuple nextState actions) = extractRequiredActionsWithTxs txInput state contract

    usefulActions = mapMaybe removeUseless actions

    slot = fromMaybe (add one currentSlot) (nextTimeout oldState)

    rawActionInputs = Map.fromFoldableWith combineChoices $ map (actionToActionInput nextState) usefulActions

    actionInputs = map simplifyActionInput rawActionInputs

    moveTo = case contract of
      Term Close _ -> Nothing
      _ -> Just $ MoveToSlot slot

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

extractRequiredActionsWithTxs :: TransactionInput -> State -> Term T.Contract -> Tuple State (Array Action)
extractRequiredActionsWithTxs txInput state contract
  | TransactionOutput { txOutContract, txOutState } <- computeTransaction txInput state contract = Tuple txOutState (extractRequiredActions txOutContract)
  | TransactionInput { inputs: Nil } <- txInput
  , IntervalTrimmed env fixState <- fixInterval (unwrap txInput).interval state
  , Just (_ /\ reducedContract) <- reduceContractUntilQuiescent env fixState contract = Tuple fixState (extractRequiredActions reducedContract)
  -- the actions remain unchanged in error cases, cases where the contract is not reduced or cases where inputs remain
  | otherwise = Tuple state (extractRequiredActions contract)

extractRequiredActions :: Term T.Contract -> Array Action
extractRequiredActions contract = case contract of
  Term (When cases _ _) _ -> map (\(S.Case action _) -> action) $ mapMaybe fromTerm cases
  _ -> mempty

applyPendingInputs :: MarloweState -> MarloweState
applyPendingInputs oldState@{ executionState: SimulationRunning executionState } = newState
  where
  txInput@(TransactionInput txIn) = pendingTransactionInputs executionState

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
    InvalidContract -> oldState
    SemanticError TEUselessTransaction -> oldState
    SemanticError txError ->
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

applyPendingInputs oldState = oldState

updateSlot :: Slot -> MarloweState -> MarloweState
updateSlot = set (_executionState <<< _SimulationRunning <<< _slot)

pendingTransactionInputs :: ExecutionStateRecord -> TransactionInput
pendingTransactionInputs executionState =
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

-- TODO: This is only being used in the ContractTests, revisit.
applyTransactions ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  m Unit
applyTransactions = modifying _marloweState (extendWith (updatePossibleActions <<< applyPendingInputs))

applyInput ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  (Array Input -> Array Input) ->
  m Unit
applyInput inputs = modifying _marloweState (extendWith (updatePossibleActions <<< applyPendingInputs <<< (over (_executionState <<< _SimulationRunning <<< _pendingInputs) inputs)))

moveToSlot ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  Slot ->
  m Unit
moveToSlot slot = do
  mSignificantSlot <- use (_marloweState <<< _Head <<< to nextTimeout)
  let
    mApplyPendingTransactions =
      if slot >= (fromMaybe zero mSignificantSlot) then
        applyPendingInputs
      else
        identity
  modifying
    _marloweState
    ( extendWith
        ( updatePossibleActions
            <<< mApplyPendingTransactions
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
    txInput = pendingTransactionInputs executionState
  in
    case fixInterval (unwrap txInput).interval (executionState ^. _state) of
      IntervalTrimmed env state' -> S.evalObservation env state' observation
      -- if there is an error in the state we will say that the observation is false.
      -- Nothing should happen anyway because applying the input will fail later
      IntervalError _ -> false

evalObservation state observation = false

nextTimeout :: MarloweState -> Maybe Slot
nextTimeout state = do
  contract <- previewOn state (_executionState <<< _SimulationRunning <<< _contract)
  let
    Timeouts { minTime } = timeouts contract
  minTime

mapPartiesActionInput :: (ActionInput -> ActionInput) -> Parties -> Parties
mapPartiesActionInput f (Parties m) = Parties $ (map <<< map) f m
