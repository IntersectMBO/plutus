module MonadApp where

import Prelude

import API (RunResult)
import Ace (Annotation, Editor)
import Ace.EditSession as Session
import Ace.Editor as AceEditor
import Auth (AuthStatus)
import Control.Monad.Except (class MonadTrans, ExceptT, runExceptT)
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.State (class MonadState)
import Data.Array (fromFoldable)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Lens (assign, modifying, over, set, to, use, (^.))
import Data.List as List
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Json.JsonEither (JsonEither)
import Data.Tuple (Tuple(..), fst)
import Editor as Editor
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import FileEvents as FileEvents
import Gist (Gist, GistId, NewGist)
import Halogen (HalogenM, liftAff, liftEffect, query')
import Halogen.Blockly (BlocklyQuery(..))
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode)
import LocalStorage as LocalStorage
import Marlowe (SPParams_)
import Marlowe as Server
import Marlowe.Parser (contract)
import Marlowe.Semantics (Contract(..), PubKey, SlotInterval(..), TransactionInput(..), TransactionOutput(..), accountOwner, choiceOwner, computeTransaction, extractRequiredActionsWithTxs, moneyInContract)
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (bufferLocalStorageKey, marloweBufferLocalStorageKey)
import Text.Parsing.Parser (ParseError(..), runParser)
import Text.Parsing.Parser.Pos (Position(..))
import Types (ActionInput(..), BlocklySlot(..), ChildQuery, ChildSlot, EditorSlot(EditorSlot), FrontendState, MarloweEditorSlot(MarloweEditorSlot), MarloweState, Query, WebData, _Head, _contract, _currentMarloweState, _editorErrors, _marloweState, _moneyInContract, _oldContract, _payments, _pendingInputs, _possibleActions, _slot, _state, _transactionError, actionToActionInput, cpBlockly, cpEditor, cpMarloweEditor, emptyMarloweState)
import Web.HTML.Event.DragEvent (DragEvent)

class
  Monad m <= MonadApp m where
  haskellEditorSetValue :: String -> Maybe Int -> m Unit
  haskellEditorGetValue :: m (Maybe String)
  haskellEditorSetAnnotations :: Array Annotation -> m Unit
  haskellEditorGotoLine :: Int -> Maybe Int -> m Unit
  marloweEditorSetValue :: String -> Maybe Int -> m Unit
  marloweEditorGetValue :: m (Maybe String)
  marloweEditorSetAnnotations :: Array Annotation -> m Unit
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

newtype HalogenApp m a
  = HalogenApp (HalogenM FrontendState Query ChildQuery ChildSlot Void m a)

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
  haskellEditorSetValue contents i = void $ withHaskellEditor $ AceEditor.setValue contents i
  haskellEditorGetValue = withHaskellEditor AceEditor.getValue
  haskellEditorSetAnnotations annotations =
    void
      $ withHaskellEditor \editor -> do
          session <- AceEditor.getSession editor
          Session.setAnnotations annotations session
  haskellEditorGotoLine row column = void $ withHaskellEditor $ AceEditor.gotoLine row column (Just true)
  marloweEditorSetValue contents i = void $ withMarloweEditor $ AceEditor.setValue contents i
  marloweEditorGetValue = withMarloweEditor AceEditor.getValue
  marloweEditorSetAnnotations annotations =
    void
      $ withMarloweEditor \editor -> do
          session <- AceEditor.getSession editor
          Session.setAnnotations annotations session
  preventDefault event = wrap $ liftEffect $ FileEvents.preventDefault event
  readFileFromDragEvent event = wrap $ liftAff $ FileEvents.readFileFromDragEvent event
  updateContractInState contract = do
    updateContractInStateImpl contract
    annotations <- use (_marloweState <<< _Head <<< _editorErrors)
    marloweEditorSetAnnotations annotations
  updateState = do
    saveInitialStateImpl
    wrap $ modifying _currentMarloweState updateStateP
  saveInitialState = saveInitialStateImpl
  updateMarloweState f = wrap $ modifying _marloweState (extendWith f)
  applyTransactions = wrap $ modifying _marloweState (extendWith updateStateP)
  resetContract = do
    newContract <- marloweEditorGetValueImpl
    wrap $ assign _marloweState $ NEL.singleton (emptyMarloweState zero)
    wrap $ assign _oldContract Nothing
    updateContractInStateImpl $ fromMaybe "" newContract
  saveBuffer text = wrap $ liftEffect $ LocalStorage.setItem bufferLocalStorageKey text
  saveMarloweBuffer text = wrap $ liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey text
  getOauthStatus = runAjax Server.getOauthStatus
  getGistByGistId gistId = runAjax $ Server.getGistsByGistId gistId
  postGist newGist = runAjax $ Server.postGists newGist
  patchGistByGistId newGist gistId = runAjax $ Server.patchGistsByGistId newGist gistId
  postContractHaskell source = runAjax $ Server.postContractHaskell source
  resizeBlockly = wrap $ query' cpBlockly BlocklySlot (Resize unit)
  setBlocklyCode source = wrap $ void $ query' cpBlockly BlocklySlot (SetCode source unit)

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
marloweEditorGetValue' = withMarloweEditor AceEditor.getValue

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
marloweEditorGetValueImpl = withMarloweEditor AceEditor.getValue

updateContractInStateImpl :: forall m. String -> HalogenApp m Unit
updateContractInStateImpl contract = modifying _currentMarloweState (updatePossibleActions <<< updateContractInStateP contract)

runHalogenApp :: forall m a. HalogenApp m a -> HalogenM FrontendState Query ChildQuery ChildSlot Void m a
runHalogenApp = unwrap

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM FrontendState Query ChildQuery ChildSlot Void m) a ->
  HalogenApp m (WebData a)
runAjax action = wrap $ RemoteData.fromEither <$> runExceptT action

withHaskellEditor ::
  forall m a.
  MonadEffect m =>
  (Editor -> Effect a) ->
  HalogenApp m (Maybe a)
withHaskellEditor = HalogenApp <<< Editor.withEditor cpEditor EditorSlot

withMarloweEditor ::
  forall m a.
  MonadEffect m =>
  (Editor -> Effect a) ->
  HalogenApp m (Maybe a)
withMarloweEditor = HalogenApp <<< Editor.withEditor cpMarloweEditor MarloweEditorSlot

updateContractInStateP :: String -> MarloweState -> MarloweState
updateContractInStateP text state = case runParser text contract of
    Right pcon -> set _editorErrors [] <<< set _contract (Just pcon) $ state
    Left error -> set _editorErrors [errorToAnnotation error] state
    where
      errorToAnnotation (ParseError msg (Position { line, column })) = { column: column, row: (line - 1), text: msg, "type": "error" }

updatePossibleActions :: MarloweState -> MarloweState
updatePossibleActions oldState =
  let contract = oldState ^. (_contract <<< to (fromMaybe Refund))
      state = oldState ^. _state
      txInput = stateToTxInput oldState
      (Tuple nextState actions) = extractRequiredActionsWithTxs txInput state contract
      actionInputs = map (actionToActionInput nextState) actions
      actionInputsMap = splitActionsByPerson actionInputs
  in set _possibleActions actionInputsMap oldState
  where

  splitActionsByPerson :: Array ActionInput -> Map PubKey (Array ActionInput)
  splitActionsByPerson actionInputs = foldl (\m actionInput -> appendValue m (actionPerson actionInput) actionInput) mempty actionInputs

  actionPerson :: ActionInput -> PubKey
  actionPerson (DepositInput accountId _ _) = (accountOwner accountId)
  actionPerson (ChoiceInput choiceId _ _) = (choiceOwner choiceId)
  -- We have a special person for notifications
  actionPerson (NotifyInput _) = "Notifications"
  
  appendValue :: forall k v. Ord k => Map k (Array v) -> k -> v -> Map k (Array v)
  appendValue m k v = Map.alter (alterMap v) k m

  alterMap :: forall v. v -> Maybe (Array v) -> Maybe (Array v)
  alterMap v Nothing = Just $ Array.singleton v
  alterMap v (Just vs) = Just $ Array.snoc vs v

updateStateP :: MarloweState -> MarloweState
updateStateP oldState = actState
  where
  txInput = stateToTxInput oldState
  actState = case computeTransaction txInput (oldState ^. _state) (oldState ^. _contract <<< to (fromMaybe Refund)) of

    (TransactionOutput {txOutWarnings, txOutPayments, txOutState, txOutContract}) ->
      (set _transactionError Nothing 
      <<< set _pendingInputs mempty 
      <<< set _state txOutState
      <<< set _contract (Just txOutContract)
      <<< set _moneyInContract (moneyInContract txOutState)
      <<< over _payments (append (fromFoldable txOutPayments))
      ) oldState
    (Error txError) -> set _transactionError (Just txError) oldState

stateToTxInput :: MarloweState -> TransactionInput
stateToTxInput ms = let slot = ms ^. _slot
                        interval = SlotInterval slot (slot + one)
                        inputs = map fst (ms ^. _pendingInputs)
                    in TransactionInput { interval: interval, inputs: (List.fromFoldable inputs)}

-- | Apply a function to the head of a non-empty list and cons the result on
extendWith :: forall a. (a -> a) -> NonEmptyList a -> NonEmptyList a
extendWith f l = NEL.cons ((f <<< NEL.head) l) l

