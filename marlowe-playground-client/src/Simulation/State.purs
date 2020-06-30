module Simulation.State where

import Control.Monad.State (class MonadState)
import Data.Array (foldl, fromFoldable, mapMaybe, uncons)
import Data.BigInteger (BigInteger)
import Data.Either (Either(..))
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Lens (Getter', Lens', modifying, over, set, to, view, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.Lens.Record (prop)
import Data.List as List
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.NonEmpty (foldl1, (:|))
import Data.NonEmptyList.Extra (extendWith)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..), fst)
import Marlowe.Holes (Holes, fromTerm)
import Marlowe.Linter (lint)
import Marlowe.Linter as L
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (AccountId, Action(..), Assets, Bound, ChoiceId(..), ChosenNum, Contract(..), Environment(..), Input, Party, Payment, PubKey, Slot, SlotInterval(..), State, Token, TransactionError, TransactionInput(..), TransactionOutput(..), TransactionWarning, _minSlot, boundFrom, computeTransaction, emptyState, evalValue, extractRequiredActionsWithTxs, moneyInContract)
import Monaco (IMarker)
import Prelude (class Eq, class Ord, Unit, append, map, mempty, min, zero, ($), (<<<), (<))

data ActionInputId
  = DepositInputId AccountId Party Token BigInteger
  | ChoiceInputId ChoiceId (Array Bound)
  | NotifyInputId

derive instance eqActionInputId :: Eq ActionInputId

derive instance ordActionInputId :: Ord ActionInputId

-- | On the front end we need Actions however we also need to keep track of the current
-- | choice that has been set for Choices
data ActionInput
  = DepositInput AccountId Party Token BigInteger
  | ChoiceInput ChoiceId (Array Bound) ChosenNum
  | NotifyInput

derive instance eqActionInput :: Eq ActionInput

derive instance ordActionInput :: Ord ActionInput

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

type MarloweState
  = { possibleActions :: Map Party (Map ActionInputId ActionInput)
    , pendingInputs :: Array (Tuple Input (Maybe PubKey))
    , transactionError :: Maybe TransactionError
    , transactionWarnings :: Array TransactionWarning
    , state :: State
    , slot :: Slot
    , moneyInContract :: Assets
    , contract :: Maybe Contract
    , editorErrors :: Array IMarker
    , editorWarnings :: Array IMarker
    , holes :: Holes
    , log :: Array MarloweEvent
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

_log :: forall s a. Lens' { log :: a | s } a
_log = prop (SProxy :: SProxy "log")

_payments :: forall s. Getter' { log :: Array MarloweEvent | s } (Array Payment)
_payments = _log <<< to (mapMaybe f)
  where
  f (InputEvent _) = Nothing

  f (OutputEvent _ payment) = Just payment

emptyMarloweState :: Slot -> MarloweState
emptyMarloweState sn =
  { possibleActions: mempty
  , pendingInputs: mempty
  , transactionError: Nothing
  , transactionWarnings: []
  , state: emptyState sn
  , slot: sn
  , moneyInContract: mempty
  , contract: Nothing
  , editorErrors: mempty
  , editorWarnings: mempty
  , holes: mempty
  , log: []
  }

updateContractInStateP :: String -> MarloweState -> MarloweState
updateContractInStateP text state = case parseContract text of
  Right parsedContract ->
    let
      lintResult = lint state.state parsedContract

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

updatePossibleActions :: MarloweState -> MarloweState
updatePossibleActions oldState =
  let
    contract = oldState ^. (_contract <<< to (fromMaybe Close))

    state = oldState ^. _state

    txInput = stateToTxInput oldState

    (Tuple nextState actions) = extractRequiredActionsWithTxs txInput state contract

    actionInputs = foldl (\acc act -> insertTuple (actionToActionInput nextState act) acc) mempty actions
  in
    over _possibleActions (updateActions actionInputs) oldState
  where
  insertTuple :: forall k v. Ord k => Tuple k v -> Map k v -> Map k v
  insertTuple (Tuple k v) m = Map.insert k v m

  updateActions :: Map ActionInputId ActionInput -> Map Party (Map ActionInputId ActionInput) -> Map Party (Map ActionInputId ActionInput)
  updateActions actionInputs oldInputs = foldlWithIndex (addButPreserveActionInputs oldInputs) mempty actionInputs

  addButPreserveActionInputs :: Map Party (Map ActionInputId ActionInput) -> ActionInputId -> Map Party (Map ActionInputId ActionInput) -> ActionInput -> Map Party (Map ActionInputId ActionInput)
  addButPreserveActionInputs oldInputs actionInputIdx m actionInput = case (actionPerson actionInput) of
    Just party -> appendValue m oldInputs party actionInputIdx actionInput
    _ -> m

  actionPerson :: ActionInput -> (Maybe Party)
  actionPerson (DepositInput _ party _ _) = Just party

  actionPerson (ChoiceInput (ChoiceId _ party) _ _) = Just party

  -- We have a special person for notifications
  actionPerson NotifyInput = Nothing

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

updateStateP :: MarloweState -> MarloweState
updateStateP oldState = actState
  where
  txInput@(TransactionInput txIn) = stateToTxInput oldState

  actState = case computeTransaction txInput (oldState ^. _state) (oldState ^. _contract <<< to (fromMaybe Close)) of
    (TransactionOutput { txOutWarnings, txOutPayments, txOutState, txOutContract }) ->
      ( set _transactionError Nothing
          <<< set _transactionWarnings (fromFoldable txOutWarnings)
          <<< set _pendingInputs mempty
          <<< set _state txOutState
          <<< set _contract (Just txOutContract)
          <<< set _moneyInContract (moneyInContract txOutState)
          <<< over _log (append (fromFoldable (map (OutputEvent txIn.interval) txOutPayments)))
          <<< over _log (append [ InputEvent txInput ])
      )
        oldState
    (Error txError) -> set _transactionError (Just txError) oldState

stateToTxInput :: MarloweState -> TransactionInput
stateToTxInput ms =
  let
    slot = ms ^. _slot

    interval = SlotInterval slot slot

    inputs = map fst (ms ^. _pendingInputs)
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

hasHistory :: forall s. { marloweState :: NonEmptyList MarloweState | s } -> Boolean
hasHistory state = state ^. (_marloweState <<< to NEL.length <<< to ((<) 1))
