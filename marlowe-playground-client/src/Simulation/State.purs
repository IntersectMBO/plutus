module Simulation.State where

import Control.Bind
import Control.Monad.State (class MonadState)
import Data.Array (fromFoldable, mapMaybe, uncons)
import Data.BigInteger (BigInteger)
import Data.Either (Either(..))
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Generic.Rep (class Generic)
import Data.Lens (Getter', Lens', Prism', Traversal', has, lens, modifying, nearly, over, preview, previewOn, prism, set, to, use, view, (^.))
import Data.Lens.At (at)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.Lens.Record (prop)
import Data.List as List
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.NonEmpty (foldl1, (:|))
import Data.NonEmptyList.Extra (extendWith)
import Data.NonEmptyList.Lens (_Tail)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Foreign.Generic (class Decode, class Encode, genericDecode, genericEncode)
import Marlowe.Holes (Holes, fromTerm)
import Marlowe.Linter (lint)
import Marlowe.Linter as L
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (AccountId, Action(..), Assets, Bound, ChoiceId(..), ChosenNum, Contract(..), Environment(..), Input, IntervalResult(..), Observation, Party(..), Payment, Slot, SlotInterval(..), State, Token, TransactionError, TransactionInput(..), TransactionOutput(..), TransactionWarning, _minSlot, aesonCompatibleOptions, boundFrom, computeTransaction, emptyState, evalValue, extractRequiredActionsWithTxs, fixInterval, moneyInContract, timeouts)
import Marlowe.Semantics as S
import Monaco (IMarker)
import Prelude (class Eq, class HeytingAlgebra, class Monoid, class Ord, class Semigroup, Unit, add, append, map, mempty, min, one, zero, (#), ($), (<<<), (==), (>))

data ActionInputId
  = DepositInputId AccountId Party Token BigInteger
  | ChoiceInputId ChoiceId (Array Bound)
  | NotifyInputId
  | MoveToSlotId

derive instance eqActionInputId :: Eq ActionInputId

derive instance ordActionInputId :: Ord ActionInputId

derive instance genericActionInputId :: Generic ActionInputId _

instance encodeActionInputId :: Encode ActionInputId where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeActionInputId :: Decode ActionInputId where
  decode = genericDecode aesonCompatibleOptions

-- | On the front end we need Actions however we also need to keep track of the current
-- | choice that has been set for Choices
data ActionInput
  = DepositInput AccountId Party Token BigInteger
  | ChoiceInput ChoiceId (Array Bound) ChosenNum
  | NotifyInput
  | MoveToSlot Slot

derive instance eqActionInput :: Eq ActionInput

derive instance ordActionInput :: Ord ActionInput

derive instance genericActionInput :: Generic ActionInput _

instance encodeActionInput :: Encode ActionInput where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeActionInput :: Decode ActionInput where
  decode = genericDecode aesonCompatibleOptions

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

actionToActionInput _ (Choice choiceId bounds) = Tuple (ChoiceInputId choiceId bounds) (ChoiceInput choiceId bounds (minimumBound bounds))

actionToActionInput _ (Notify _) = Tuple NotifyInputId NotifyInput

data MarloweEvent
  = InputEvent TransactionInput
  | OutputEvent SlotInterval Payment

derive instance genericMarloweEvent :: Generic MarloweEvent _

instance encodeMarloweEvent :: Encode MarloweEvent where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeMarloweEvent :: Decode MarloweEvent where
  decode = genericDecode aesonCompatibleOptions

newtype Parties
  = Parties (Map Party (Map ActionInputId ActionInput))

derive instance newtypeParties :: Newtype Parties _

derive newtype instance semigroupParties :: Semigroup Parties

derive newtype instance monoidParties :: Monoid Parties

mapPartiesActionInput :: (ActionInput -> ActionInput) -> Parties -> Parties
mapPartiesActionInput f (Parties m) = Parties $ (map <<< map) f m

derive newtype instance encodeParties :: Encode Parties

derive newtype instance decodeParties :: Decode Parties

_actionInput :: Party -> ActionInputId -> Traversal' Parties ActionInput
_actionInput party id = _Newtype <<< ix party <<< ix id

_otherActions :: Traversal' Parties (Map ActionInputId ActionInput)
_otherActions = _Newtype <<< ix otherActionsParty

_moveToAction :: Lens' Parties (Maybe ActionInput)
_moveToAction = lens get' set'
  where
  get' = preview (_actionInput otherActionsParty MoveToSlotId)

  set' p ma =
    let
      m = case preview _otherActions p, ma of
        Nothing, Nothing -> Nothing
        Just m', Nothing -> Just $ Map.delete MoveToSlotId m'
        Nothing, Just a -> Just $ Map.singleton MoveToSlotId a
        Just m', Just a -> Just $ Map.insert MoveToSlotId a m'
    in
      set (_Newtype <<< at otherActionsParty) m p

type ExecutionStateRecord
  = { possibleActions :: Parties
    , pendingInputs :: Array Input
    , transactionError :: Maybe TransactionError
    , transactionWarnings :: Array TransactionWarning
    , log :: Array MarloweEvent
    , state :: State
    , slot :: Slot
    , moneyInContract :: Assets
    }

_possibleActions :: forall s a. Lens' { possibleActions :: a | s } a
_possibleActions = prop (SProxy :: SProxy "possibleActions")

_pendingInputs :: forall s a. Lens' { pendingInputs :: a | s } a
_pendingInputs = prop (SProxy :: SProxy "pendingInputs")

_state :: forall s a. Lens' { state :: a | s } a
_state = prop (SProxy :: SProxy "state")

_transactionError :: forall s a. Lens' { transactionError :: a | s } a
_transactionError = prop (SProxy :: SProxy "transactionError")

_transactionWarnings :: forall s a. Lens' { transactionWarnings :: a | s } a
_transactionWarnings = prop (SProxy :: SProxy "transactionWarnings")

_slot :: forall s a. Lens' { slot :: a | s } a
_slot = prop (SProxy :: SProxy "slot")

_moneyInContract :: forall s a. Lens' { moneyInContract :: a | s } a
_moneyInContract = prop (SProxy :: SProxy "moneyInContract")

_log :: forall s a. Lens' { log :: a | s } a
_log = prop (SProxy :: SProxy "log")

_payments :: forall s. Getter' { log :: Array MarloweEvent | s } (Array Payment)
_payments = _log <<< to (mapMaybe f)
  where
  f (InputEvent _) = Nothing

  f (OutputEvent _ payment) = Just payment

type InitialConditionsRecord
  = { initialSlot :: Slot }

_initialSlot :: forall s a. Lens' { initialSlot :: a | s } a
_initialSlot = prop (SProxy :: SProxy "initialSlot")

data ExecutionState
  = SimulationRunning ExecutionStateRecord
  | SimulationNotStarted InitialConditionsRecord

-- | Prism for the `ExecutionState` constructor of `SimulationRunning`.
_SimulationRunning :: Prism' ExecutionState ExecutionStateRecord
_SimulationRunning =
  prism SimulationRunning
    $ ( \x -> case x of
          SimulationRunning record -> Right record
          anotherCase -> Left anotherCase
      )

-- | Prism for the `ExecutionState` constructor of `SimulationNotStarted`.
_SimulationNotStarted :: Prism' ExecutionState InitialConditionsRecord
_SimulationNotStarted =
  prism SimulationNotStarted
    $ ( \x -> case x of
          SimulationNotStarted record -> Right record
          anotherCase -> Left anotherCase
      )

emptyExecutionStateWithSlot :: Slot -> ExecutionState
emptyExecutionStateWithSlot sn =
  SimulationRunning
    { possibleActions: mempty
    , pendingInputs: mempty
    , transactionError: Nothing
    , transactionWarnings: mempty
    , log: mempty
    , state: emptyState sn
    , slot: sn
    , moneyInContract: mempty
    }

simulationNotStartedWithSlot :: Slot -> ExecutionState
simulationNotStartedWithSlot slot = SimulationNotStarted { initialSlot: slot }

simulationNotStarted :: ExecutionState
simulationNotStarted = simulationNotStartedWithSlot zero

type MarloweState
  = { executionState :: ExecutionState
    , contract :: Maybe Contract
    , editorErrors :: Array IMarker
    , editorWarnings :: Array IMarker
    , holes :: Holes
    }

_executionState :: forall s a. Lens' { executionState :: a | s } a
_executionState = prop (SProxy :: SProxy "executionState")

_contract :: forall s a. Lens' { contract :: a | s } a
_contract = prop (SProxy :: SProxy "contract")

_editorErrors :: forall s a. Lens' { editorErrors :: a | s } a
_editorErrors = prop (SProxy :: SProxy "editorErrors")

_editorWarnings :: forall s a. Lens' { editorWarnings :: a | s } a
_editorWarnings = prop (SProxy :: SProxy "editorWarnings")

_holes :: forall s a. Lens' { holes :: a | s } a
_holes = prop (SProxy :: SProxy "holes")

--- Language.Haskell.Interpreter ---
_result :: forall s a. Lens' { result :: a | s } a
_result = prop (SProxy :: SProxy "result")

emptyMarloweState :: MarloweState
emptyMarloweState =
  { contract: Nothing
  , editorErrors: mempty
  , editorWarnings: mempty
  , holes: mempty
  , executionState: simulationNotStarted
  }

emptyMarloweStateWithSlot :: Slot -> MarloweState
emptyMarloweStateWithSlot sn =
  { contract: Nothing
  , editorErrors: mempty
  , editorWarnings: mempty
  , holes: mempty
  , executionState: emptyExecutionStateWithSlot sn
  }

getAsMuchStateAP :: forall m t0. MonadState { marloweState :: NonEmptyList MarloweState | t0 } m => m State
getAsMuchStateAP = do
  executionState <- use (_currentMarloweState <<< _executionState)
  pure
    ( case executionState of
        SimulationRunning runRecord -> runRecord.state
        SimulationNotStarted notRunRecord -> emptyState notRunRecord.initialSlot
    )

inFuture :: forall b r. HeytingAlgebra b => { marloweState :: NonEmptyList MarloweState | r } -> Slot -> b
inFuture state slot = has (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _slot <<< nearly zero ((>) slot)) state

-- We have a special person for notifications
otherActionsParty :: Party
otherActionsParty = Role "marlowe_other_actions"

updateContractInStateP :: String -> MarloweState -> MarloweState
updateContractInStateP text state = case parseContract text of
  Right parsedContract ->
    let
      lintResult = lint marloweState parsedContract

      mContract = fromTerm parsedContract
    in
      case mContract of
        Just contract -> do
          set _editorErrors [] <<< set _contract (Just contract) $ state
        Nothing -> do
          let
            holes = view L._holes lintResult
          (set _holes holes) state
  Left error -> (set _holes mempty) state
  where
  marloweState = fromMaybe (emptyState zero) (previewOn state (_executionState <<< _SimulationRunning <<< _state))

updatePossibleActions :: MarloweState -> MarloweState
updatePossibleActions oldState@{ executionState: SimulationRunning executionState } =
  let
    contract = fromMaybe Close (oldState ^. _contract)

    state = executionState ^. _state

    currentSlot = executionState ^. _slot

    txInput = stateToTxInput executionState

    (Tuple nextState actions) = extractRequiredActionsWithTxs txInput state contract

    usefulActions = mapMaybe removeUseless actions

    slot = fromMaybe (add one currentSlot) (nextSignificantSlot oldState)

    actionInputs = Map.fromFoldable $ map (actionToActionInput nextState) usefulActions

    moveTo = if contract == Close then Nothing else Just $ MoveToSlot slot

    newExecutionState =
      executionState # over _possibleActions (updateActions actionInputs)
        # set (_possibleActions <<< _moveToAction) moveTo
  in
    oldState # set _executionState (SimulationRunning newExecutionState)
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

updateStateP :: MarloweState -> MarloweState
updateStateP oldState@{ executionState: SimulationRunning executionState } = actState
  where
  txInput@(TransactionInput txIn) = stateToTxInput executionState

  actState = case computeTransaction txInput (executionState ^. _state) (oldState ^. _contract <<< to (fromMaybe Close)) of
    (TransactionOutput { txOutWarnings, txOutPayments, txOutState, txOutContract }) ->
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
        ( set _executionState (SimulationRunning newExecutionState)
            <<< set _contract (Just txOutContract)
        )
          oldState
    (Error txError) ->
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

stateToTxInput :: ExecutionStateRecord -> TransactionInput
stateToTxInput executionState =
  let
    slot = executionState ^. _slot

    interval = SlotInterval slot slot

    inputs = executionState ^. _pendingInputs
  in
    TransactionInput { interval: interval, inputs: (List.fromFoldable inputs) }

--
-- Functions that can be used by records that contain MarloweState
--
_marloweState :: forall s. Lens' { marloweState :: NonEmptyList MarloweState | s } (NonEmptyList MarloweState)
_marloweState = prop (SProxy :: SProxy "marloweState")

_currentMarloweState :: forall s. Lens' { marloweState :: NonEmptyList MarloweState | s } MarloweState
_currentMarloweState = _marloweState <<< _Head

updateMarloweState :: forall s m. MonadState { marloweState :: NonEmptyList MarloweState | s } m => (MarloweState -> MarloweState) -> m Unit
updateMarloweState f = modifying _marloweState (extendWith (updatePossibleActions <<< f))

updateContractInState :: forall s m. MonadState { marloweState :: NonEmptyList MarloweState | s } m => String -> m Unit
updateContractInState contents = modifying _currentMarloweState (updatePossibleActions <<< updateContractInStateP contents)

applyTransactions :: forall s m. MonadState { marloweState :: NonEmptyList MarloweState | s } m => m Unit
applyTransactions = modifying _marloweState (extendWith (updatePossibleActions <<< updateStateP))

applyInput ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  (Array Input -> Array Input) ->
  m Unit
applyInput inputs = modifying _marloweState (extendWith (updatePossibleActions <<< updateStateP <<< (over (_executionState <<< _SimulationRunning <<< _pendingInputs) inputs)))

moveToSignificantSlot ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  Slot ->
  m Unit
moveToSignificantSlot slot = modifying _marloweState (extendWith (updatePossibleActions <<< updateStateP <<< (set (_executionState <<< _SimulationRunning <<< _slot) slot)))

moveToSlot ::
  forall s m.
  MonadState { marloweState :: NonEmptyList MarloweState | s } m =>
  Slot ->
  m Unit
moveToSlot slot = modifying _marloweState (extendWith (updatePossibleActions <<< (set (_executionState <<< _SimulationRunning <<< _slot) slot)))

hasHistory :: forall s. { marloweState :: NonEmptyList MarloweState | s } -> Boolean
hasHistory state = has (_marloweState <<< _Tail) state

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

nextSignificantSlot :: MarloweState -> Maybe Slot
nextSignificantSlot state =
  state
    ^. ( _contract
          <<< to (fromMaybe Close)
          <<< to timeouts
          <<< to unwrap
          <<< to _.minTime
      )
