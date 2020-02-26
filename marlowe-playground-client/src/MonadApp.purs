module MonadApp where

import Prelude
import API (RunResult)
import Ace (Annotation, Editor)
import Ace as Ace
import Ace.EditSession as Session
import Ace.Editor as AceEditor
import Auth (AuthStatus)
import Control.Monad.Except (class MonadTrans, ExceptT, runExceptT)
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.State (class MonadState)
import Data.Array (fold, fromFoldable, take)
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Json.JsonEither (JsonEither)
import Data.Lens (assign, modifying, over, set, to, use, view, (^.))
import Data.List as List
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Set as Set
import Data.String.Extra (unlines)
import Data.Tuple (Tuple(..), fst)
import Editor as Editor
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import FileEvents as FileEvents
import Foreign.Class (encode)
import Gist (Gist, GistId, NewGist)
import Global.Unsafe (unsafeStringify)
import Halogen (HalogenM, liftAff, liftEffect, query, raise)
import Halogen.Blockly (BlocklyQuery(..))
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode)
import Marlowe (SPParams_)
import Marlowe as Server
import Marlowe.Holes (Holes(..), MarloweHole(..), fromTerm)
import Marlowe.Linter (Position, lint)
import Marlowe.Linter as L
import Marlowe.Parser (ContractParseError(..), parseContract)
import Marlowe.Semantics (ChoiceId(..), Contract(..), Party(..), PubKey, SlotInterval(..), TransactionInput(..), TransactionOutput(..), computeTransaction, extractRequiredActionsWithTxs, moneyInContract)
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (bufferLocalStorageKey, marloweBufferLocalStorageKey)
import Text.Parsing.StringParser.Basic (lines)
import Types (ActionInput(..), ActionInputId, ChildSlots, FrontendState, HAction, MarloweState, WebData, Message(..), _Head, _blocklySlot, _contract, _currentMarloweState, _editorErrors, _haskellEditorSlot, _holes, _marloweEditorSlot, _marloweState, _moneyInContract, _oldContract, _payments, _pendingInputs, _possibleActions, _slot, _state, _transactionError, _transactionWarnings, actionToActionInput, emptyMarloweState)
import Web.HTML.Event.DragEvent (DragEvent)
import WebSocket (WebSocketRequestMessage(CheckForWarnings))

class
  Monad m <= MonadApp m where
  haskellEditorSetValue :: String -> Maybe Int -> m Unit
  haskellEditorGetValue :: m (Maybe String)
  haskellEditorHandleAction :: Editor.Action -> m Unit
  haskellEditorSetAnnotations :: Array Annotation -> m Unit
  marloweEditorSetValue :: String -> Maybe Int -> m Unit
  marloweEditorGetValue :: m (Maybe String)
  marloweEditorHandleAction :: Editor.Action -> m Unit
  marloweEditorSetAnnotations :: Array Annotation -> m Unit
  marloweEditorMoveCursorToPosition :: Ace.Position -> m Unit
  preventDefault :: DragEvent -> m Unit
  readFileFromDragEvent :: DragEvent -> m String
  updateContractInState :: String -> m Unit
  updateState :: m Unit
  saveInitialState :: m Unit
  updateMarloweState :: (MarloweState -> MarloweState) -> m Unit
  applyTransactions :: m Unit
  resetContract :: m Unit
  saveBuffer :: String -> m Unit
  saveMarloweBuffer :: String -> m Unit
  getOauthStatus :: m (WebData AuthStatus)
  getGistByGistId :: GistId -> m (WebData Gist)
  postGist :: NewGist -> m (WebData Gist)
  patchGistByGistId :: NewGist -> GistId -> m (WebData Gist)
  postContractHaskell :: SourceCode -> m (WebData (JsonEither InterpreterError (InterpreterResult RunResult)))
  resizeBlockly :: m (Maybe Unit)
  setBlocklyCode :: String -> m Unit
  checkContractForWarnings :: String -> m Unit

newtype HalogenApp m a
  = HalogenApp (HalogenM FrontendState HAction ChildSlots Message m a)

derive instance newtypeHalogenApp :: Newtype (HalogenApp m a) _

derive newtype instance functorHalogenApp :: Functor (HalogenApp m)

derive newtype instance applicativeHalogenApp :: Applicative (HalogenApp m)

derive newtype instance applyHalogenApp :: Apply (HalogenApp m)

derive newtype instance bindHalogenApp :: Bind (HalogenApp m)

derive newtype instance monadHalogenApp :: Monad (HalogenApp m)

derive newtype instance monadTransHalogenApp :: MonadTrans HalogenApp

derive newtype instance monadAskHalogenApp :: MonadAsk env m => MonadAsk env (HalogenApp m)

derive newtype instance monadStateHalogenApp :: MonadState FrontendState (HalogenApp m)

instance monadAppHalogenApp ::
  ( MonadEffect m
  , MonadAsk (SPSettings_ SPParams_) m
  , MonadAff m
  ) =>
  MonadApp (HalogenApp m) where
  haskellEditorSetValue contents i = void $ withHaskellEditor $ liftEffect <<< AceEditor.setValue contents i
  haskellEditorGetValue = withHaskellEditor $ liftEffect <<< AceEditor.getValue
  haskellEditorHandleAction action = void $ withHaskellEditor $ Editor.handleAction bufferLocalStorageKey action
  haskellEditorSetAnnotations annotations =
    void
      $ withHaskellEditor \editor ->
          liftEffect do
            session <- AceEditor.getSession editor
            Session.setAnnotations annotations session
  marloweEditorSetValue contents i = void $ withMarloweEditor $ liftEffect <<< AceEditor.setValue contents i
  marloweEditorGetValue = withMarloweEditor $ liftEffect <<< AceEditor.getValue
  marloweEditorHandleAction action = void $ withMarloweEditor (Editor.handleAction marloweBufferLocalStorageKey action)
  marloweEditorSetAnnotations annotations =
    let
      changeIndex { column, row, text, "type": t } = { column, row: row - 1, text, "type": t }
    in
      void
        $ withMarloweEditor \editor ->
            liftEffect do
              session <- AceEditor.getSession editor
              Session.setAnnotations (map changeIndex annotations) session
  marloweEditorMoveCursorToPosition (Ace.Position { column, row }) = do
    void $ withMarloweEditor $ liftEffect <<< AceEditor.focus
    void $ withMarloweEditor $ liftEffect <<< AceEditor.navigateTo (row - 1) (column - 1)
  preventDefault event = wrap $ liftEffect $ FileEvents.preventDefault event
  readFileFromDragEvent event = wrap $ liftAff $ FileEvents.readFileFromDragEvent event
  updateContractInState contract = do
    updateContractInStateImpl contract
    annotations <- use (_marloweState <<< _Head <<< _editorErrors)
    marloweEditorSetAnnotations annotations
  updateState = do
    saveInitialStateImpl
    wrap $ modifying _currentMarloweState updateStateImpl
  saveInitialState = saveInitialStateImpl
  updateMarloweState f = wrap $ modifying _marloweState (extendWith (updatePossibleActions <<< f))
  applyTransactions = wrap $ modifying _marloweState (extendWith updateStateImpl)
  resetContract = do
    newContract <- marloweEditorGetValueImpl
    wrap $ assign _marloweState $ NEL.singleton (emptyMarloweState zero)
    wrap $ assign _oldContract Nothing
    updateContractInStateImpl $ fromMaybe "" newContract
  saveBuffer text = wrap $ Editor.saveBuffer bufferLocalStorageKey text
  saveMarloweBuffer text = wrap $ Editor.saveBuffer marloweBufferLocalStorageKey text
  getOauthStatus = runAjax Server.getOauthStatus
  getGistByGistId gistId = runAjax $ Server.getGistsByGistId gistId
  postGist newGist = runAjax $ Server.postGists newGist
  patchGistByGistId newGist gistId = runAjax $ Server.patchGistsByGistId newGist gistId
  postContractHaskell source = runAjax $ Server.postContractHaskell source
  resizeBlockly = wrap $ query _blocklySlot unit (Resize unit)
  setBlocklyCode source = wrap $ void $ query _blocklySlot unit (SetCode source unit)
  checkContractForWarnings contract = do
    let
      msgString = unsafeStringify <<< encode $ CheckForWarnings contract
    wrap $ raise (WebsocketMessage msgString)

-- I don't quite understand why but if you try to use MonadApp methods in HalogenApp methods you
-- blow the stack so we have 3 methods pulled out here. I think this just ensures they are run
-- in the HalogenApp monad and that's all that's required although a type annotation inside the
-- monad doesn't seem to help, neither does `wrap . runHalogenApp`
saveInitialState' :: forall m. MonadEffect m => HalogenApp m Unit
saveInitialState' = do
  oldContract <- marloweEditorGetValue'
  modifying _oldContract
    ( \x -> case x of
        Nothing ->
          Just
            ( case oldContract of
                Nothing -> ""
                Just y -> y
            )
        _ -> x
    )

marloweEditorGetValue' :: forall m. MonadEffect m => HalogenApp m (Maybe String)
marloweEditorGetValue' = withMarloweEditor $ liftEffect <<< AceEditor.getValue

updateContractInState' :: forall m. String -> HalogenApp m Unit
updateContractInState' contract = modifying _currentMarloweState (updateStateP <<< updateContractInStateP contract)

-- I don't quite understand why but if you try to use MonadApp methods in HalogenApp methods you
-- blow the stack so we have 3 methods pulled out here. I think this just ensures they are run
-- in the HalogenApp monad and that's all that's required although a type annotation inside the
-- monad doesn't seem to help, neither does `wrap . runHalogenApp`
saveInitialStateImpl :: forall m. MonadEffect m => HalogenApp m Unit
saveInitialStateImpl = do
  oldContract <- marloweEditorGetValueImpl
  modifying _oldContract
    ( \x -> case x of
        Nothing -> Just $ fromMaybe "" oldContract
        _ -> x
    )

marloweEditorGetValueImpl :: forall m. MonadEffect m => HalogenApp m (Maybe String)
marloweEditorGetValueImpl = withMarloweEditor $ liftEffect <<< AceEditor.getValue

updateContractInStateImpl :: forall m. String -> HalogenApp m Unit
updateContractInStateImpl contract = modifying _currentMarloweState (updatePossibleActions <<< updateContractInStateP contract)

runHalogenApp :: forall m a. HalogenApp m a -> HalogenM FrontendState HAction ChildSlots Message m a
runHalogenApp = unwrap

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM FrontendState HAction ChildSlots Message m) a ->
  HalogenApp m (WebData a)
runAjax action = wrap $ RemoteData.fromEither <$> runExceptT action

withHaskellEditor ::
  forall m a.
  MonadEffect m =>
  (Editor -> m a) ->
  HalogenApp m (Maybe a)
withHaskellEditor = HalogenApp <<< Editor.withEditor _haskellEditorSlot unit

withMarloweEditor ::
  forall m a.
  MonadEffect m =>
  (Editor -> m a) ->
  HalogenApp m (Maybe a)
withMarloweEditor = HalogenApp <<< Editor.withEditor _marloweEditorSlot unit

updateContractInStateP :: String -> MarloweState -> MarloweState
updateContractInStateP text state = case parseContract text of
  Right parsedContract ->
    let
      lintResult = lint parsedContract

      warnings =
        map (warningToAnnotation text "The contract can make a negative payment here") (view L._negativePayments lintResult)
          <> map (warningToAnnotation text "The contract can make a negative deposit here") (view L._negativeDeposits lintResult)
          <> map (warningToAnnotation text "Timeouts should always increase in value") (view L._timeoutNotIncreasing lintResult)
          <> map (warningToAnnotation text "The contract tries to Use a ValueId that has not been defined in a Let") (view L._uninitializedUse lintResult)
          <> map (warningToAnnotation text "Let is redefining a ValueId that already exists") (view L._shadowedLet lintResult)
          <> map (warningToAnnotation text "This Observation will always evaluate to True") (view L._trueObservation lintResult)
          <> map (warningToAnnotation text "This Observation will always evaluate to False") (view L._falseObservation lintResult)

      mContract = fromTerm parsedContract
    in
      case mContract of
        Just contract -> do
          set _editorErrors warnings <<< set _contract (Just contract) $ state
        Nothing -> do
          let
            (Holes holes) = view L._holes lintResult

            holesArray = Set.toUnfoldable $ fold $ Map.values holes

            errors = warnings <> map (holeToAnnotation text) holesArray
          (set _editorErrors errors <<< set _holes (Holes holes)) state
  Left error -> (set _editorErrors [ errorToAnnotation text error ] <<< set _holes mempty) state

warningToAnnotation :: String -> String -> Position -> Annotation
warningToAnnotation str text { row, column } = { column, row, text, "type": "warning" }

holeToAnnotation :: String -> MarloweHole -> Annotation
holeToAnnotation str (MarloweHole { name, marloweType, row, column }) = { column, row, text: "Found hole ?" <> name, "type": "warning" }

errorToAnnotation :: String -> ContractParseError -> Annotation
errorToAnnotation str EmptyInput = { column: 0, row: 0, text: "No input provided", "type": "error" }

errorToAnnotation str (ContractParseError { row, column, message, token }) =
  let
    msg = unlines $ take 4 $ lines message
  in
    { column, row, text: msg, "type": "error" }

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

  updateActions :: Map ActionInputId ActionInput -> Map (Maybe PubKey) (Map ActionInputId ActionInput) -> Map (Maybe PubKey) (Map ActionInputId ActionInput)
  updateActions actionInputs oldInputs = foldlWithIndex (addButPreserveActionInputs oldInputs) mempty actionInputs

  addButPreserveActionInputs :: Map (Maybe PubKey) (Map ActionInputId ActionInput) -> ActionInputId -> Map (Maybe PubKey) (Map ActionInputId ActionInput) -> ActionInput -> Map (Maybe PubKey) (Map ActionInputId ActionInput)
  addButPreserveActionInputs oldInputs actionInputIdx m actionInput = appendValue m oldInputs (actionPerson actionInput) actionInputIdx actionInput

  actionPerson :: ActionInput -> (Maybe PubKey)
  actionPerson (DepositInput _ (PK party) _ _) = Just party

  actionPerson (DepositInput _ (Role party) _ _) = Just party

  actionPerson (ChoiceInput (ChoiceId _ (PK pubKey)) _ _) = Just pubKey

  actionPerson (ChoiceInput (ChoiceId _ (Role role)) _ _) = Just role

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

updateStateImpl :: MarloweState -> MarloweState
updateStateImpl = updatePossibleActions <<< updateStateP

updateStateP :: MarloweState -> MarloweState
updateStateP oldState = actState
  where
  txInput = stateToTxInput oldState

  actState = case computeTransaction txInput (oldState ^. _state) (oldState ^. _contract <<< to (fromMaybe Close)) of
    (TransactionOutput { txOutWarnings, txOutPayments, txOutState, txOutContract }) ->
      ( set _transactionError Nothing
          <<< set _transactionWarnings (fromFoldable txOutWarnings)
          <<< set _pendingInputs mempty
          <<< set _state txOutState
          <<< set _contract (Just txOutContract)
          <<< set _moneyInContract (moneyInContract txOutState)
          <<< over _payments (append (fromFoldable txOutPayments))
      )
        oldState
    (Error txError) -> set _transactionError (Just txError) oldState

stateToTxInput :: MarloweState -> TransactionInput
stateToTxInput ms =
  let
    slot = ms ^. _slot

    interval = SlotInterval slot (slot + one)

    inputs = map fst (ms ^. _pendingInputs)
  in
    TransactionInput { interval: interval, inputs: (List.fromFoldable inputs) }

-- | Apply a function to the head of a non-empty list and cons the result on
extendWith :: forall a. (a -> a) -> NonEmptyList a -> NonEmptyList a
extendWith f l = NEL.cons ((f <<< NEL.head) l) l
