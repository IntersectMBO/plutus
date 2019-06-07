module MonadApp where

import Prelude
import Ace (Editor, Annotation)
import Ace.Editor as AceEditor
import Ace.EditSession as Session
import Ace.Halogen.Component (AceQuery(..))
import API (RunResult)
import Auth (AuthStatus)
import Control.Monad.Except (class MonadTrans, ExceptT, runExceptT)
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.State (class MonadState)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Either (Either(..))
import Data.Foldable (foldrDefault)
import Data.Functor (mapFlipped)
import Data.Functor.Coproduct (Coproduct)
import Data.Lens (assign, modifying, over, set)
import Data.List (List(..))
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.RawJson (JsonEither)
import Data.Set (Set)
import Data.Set as Set
import Editor as Editor
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import FileEvents as FileEvents
import Gist (Gist, GistId, NewGist)
import Halogen (HalogenM, liftAff, liftEffect, query', request)
import Halogen.Component.ChildPath (ChildPath)
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode)
import LocalStorage as LocalStorage
import Marlowe.Parser (contract)
import Marlowe.Semantics (ErrorResult(InvalidInput), IdInput(IdOracle, InputIdChoice), MApplicationResult(MCouldNotApply, MSuccessfullyApplied), OracleDataPoint(..), State(State), TransactionOutcomes, applyTransaction, collectNeededInputs, emptyState, peopleFromStateAndContract, reduce, scoutPrimitives)
import Marlowe.Types (BlockNumber, Choice, Contract(Null), IdChoice(IdChoice), IdOracle, Person, WIdChoice(WIdChoice))
import Meadow (SPParams_)
import Meadow as Server
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (bufferLocalStorageKey, marloweBufferLocalStorageKey)
import Text.Parsing.Parser (runParser)
import Types (ChildQuery, ChildSlot, EditorSlot(EditorSlot), FrontendState, InputData, MarloweEditorSlot(MarloweEditorSlot), MarloweState, OracleEntry, Query, TransactionData, TransactionValidity(..), WebData, _choiceData, _contract, _currentMarloweState, _input, _inputs, _marloweState, _oldContract, _oracleData, _outcomes, _signatures, _transaction, _validity, cpEditor, cpMarloweEditor)
import Web.HTML.Event.DragEvent (DragEvent)

class
  Monad m <= MonadApp m where
  editorSetValue :: String -> Maybe Int -> m Unit
  editorGetValue :: m (Maybe String)
  editorSetAnnotations :: Array Annotation -> m Unit
  editorGotoLine :: Int -> Maybe Int -> m Unit
  marloweEditorSetValue :: String -> Maybe Int -> m Unit
  marloweEditorGetValue :: m (Maybe String)
  preventDefault :: DragEvent -> m Unit
  readFileFromDragEvent :: DragEvent -> m String
  updateContractInState :: String -> m Unit
  updateState :: m Unit
  saveInitialState :: m Unit
  updateMarloweState :: (MarloweState -> MarloweState) -> m Unit
  resetContract :: m Unit
  saveBuffer :: String -> m Unit
  saveMarloweBuffer :: String -> m Unit
  getOauthStatus :: m (WebData AuthStatus)
  getGistByGistId :: GistId -> m (WebData Gist)
  postGist :: NewGist -> m (WebData Gist)
  patchGistByGistId :: NewGist -> GistId -> m (WebData Gist)
  postContractHaskell :: SourceCode -> m (WebData (JsonEither InterpreterError (InterpreterResult RunResult)))

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
  editorSetValue contents i = void $ withEditor $ AceEditor.setValue contents i
  editorGetValue = withEditor AceEditor.getValue
  editorSetAnnotations annotations =
    void
      $ withEditor \editor -> do
          session <- AceEditor.getSession editor
          Session.setAnnotations annotations session
  editorGotoLine row column = void $ withEditor $ AceEditor.gotoLine row column (Just true)
  marloweEditorSetValue contents i = void $ withMarloweEditor $ AceEditor.setValue contents i
  marloweEditorGetValue = withMarloweEditor AceEditor.getValue
  preventDefault event = wrap $ liftEffect $ FileEvents.preventDefault event
  readFileFromDragEvent event = wrap $ liftAff $ FileEvents.readFileFromDragEvent event
  updateContractInState contract = wrap $ modifying _currentMarloweState (updateStateP <<< updateContractInStateP contract)
  updateState = do
    saveInitialState
    wrap $ modifying _currentMarloweState updateStateP
  saveInitialState = do
    oldContract <- editorGetValue
    wrap
      $ modifying _oldContract
          ( \x -> case x of
            Nothing ->
              Just
                ( case oldContract of
                  Nothing -> ""
                  Just y -> y
                )
            _ -> x
          )
  updateMarloweState f = wrap $ modifying _marloweState (extendWith (updateStateP <<< f))
  resetContract = do
    newContract <- editorGetValue
    wrap $ assign _marloweState $ NEL.singleton emptyMarloweState
    wrap $ assign _oldContract Nothing
    updateContractInState
      ( case newContract of
        Nothing -> ""
        Just x -> x
      )
  saveBuffer text = wrap $ liftEffect $ LocalStorage.setItem bufferLocalStorageKey text
  saveMarloweBuffer text = wrap $ liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey text
  getOauthStatus = runAjax Server.getOauthStatus
  getGistByGistId gistId = runAjax $ Server.getGistsByGistId gistId
  postGist newGist = runAjax $ Server.postGists newGist
  patchGistByGistId newGist gistId = runAjax $ Server.patchGistsByGistId newGist gistId
  postContractHaskell source = runAjax $ Server.postContractHaskell source

runHalogenApp :: forall m a. HalogenApp m a -> HalogenM FrontendState Query (Coproduct AceQuery AceQuery) (Either EditorSlot MarloweEditorSlot) Void m a
runHalogenApp = unwrap

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM FrontendState Query (Coproduct AceQuery AceQuery) (Either EditorSlot MarloweEditorSlot) Void m) a ->
  HalogenApp m (WebData a)
runAjax action = wrap $ RemoteData.fromEither <$> runExceptT action

withEditor ::
  forall m a.
  MonadEffect m =>
  (Editor -> Effect a) ->
  HalogenApp m (Maybe a)
withEditor = HalogenApp <<< Editor.withEditor cpEditor EditorSlot

withMarloweEditor ::
  forall m a.
  MonadEffect m =>
  (Editor -> Effect a) ->
  HalogenApp m (Maybe a)
withMarloweEditor = HalogenApp <<< Editor.withEditor cpMarloweEditor MarloweEditorSlot

updateContractInStateP :: String -> MarloweState -> MarloweState
updateContractInStateP text state = set _contract con state
  where
  con = case runParser text contract of
    Right pcon -> Just pcon
    Left _ -> Nothing

updateStateP :: MarloweState -> MarloweState
updateStateP oldState = actState
  where
  sigState = updateSignatures oldState

  mSimulatedState = simulateState sigState

  actState = case mSimulatedState of
    Just simulatedState -> updateActions sigState simulatedState
    Nothing -> sigState

updateSignatures :: MarloweState -> MarloweState
updateSignatures oldState = case oldState.contract of
  Just oldContract -> over (_transaction <<< _signatures) (resizeSigs (peopleFromStateAndContract (oldState.state) oldContract)) oldState
  Nothing -> oldState

simulateState :: MarloweState -> Maybe {state :: State, contract :: Contract, outcome :: TransactionOutcomes, validity :: TransactionValidity}
simulateState state =
  mapFlipped state.contract \c -> case inps, applyTransaction inps sigs bn st c mic of
    _, MSuccessfullyApplied {state: newState, contract: newContract, outcome: outcome} inputWarnings ->
      { state: newState
      , contract: newContract
      , outcome: outcome
      , validity: ValidTransaction inputWarnings
      }
    Nil, MCouldNotApply InvalidInput ->
      { state: st
      , contract: reduce state.blockNum state.state c
      , outcome: Map.empty
      , validity: EmptyTransaction
      }
    _, MCouldNotApply InvalidInput ->
      { state: emptyState
      , contract: Null
      , outcome: Map.empty
      , validity: InvalidTransaction InvalidInput
      }
    _, MCouldNotApply err ->
      { state: emptyState
      , contract: Null
      , outcome: Map.empty
      , validity: InvalidTransaction err
      }
  where
  inps = Array.toUnfoldable (state.transaction.inputs)

  sigs = Set.fromFoldable (Map.keys (Map.filter identity (state.transaction.signatures)))

  bn = state.blockNum

  st = state.state

  mic = state.moneyInContract

updateActions :: MarloweState -> {state :: State, contract :: Contract, outcome :: TransactionOutcomes, validity :: TransactionValidity} -> MarloweState
updateActions oldState {state, contract, outcome, validity} =
  set (_transaction <<< _validity) validity oldState
    # set (_transaction <<< _outcomes) outcome
    # over (_input <<< _oracleData) (updateOracles oldState.blockNum state neededInputs)
    # over (_input <<< _choiceData) (updateChoices state neededInputs)
    # set (_input <<< _inputs) (scoutPrimitives oldState.blockNum state contract)
  where
  neededInputs = collectNeededInputs contract

updateOracles :: BlockNumber -> State -> Set IdInput -> Map IdOracle OracleEntry -> Map IdOracle OracleEntry
updateOracles cbn (State state) inputs omap = foldrDefault addOracle Map.empty inputs
  where
  addOracle (IdOracle idOracle) a = case Map.lookup idOracle omap, Map.lookup idOracle state.oracles of
    Nothing, Nothing -> Map.insert idOracle {blockNumber: cbn, value: zero} a
    Just {blockNumber: bn, value}, Just (OracleDataPoint {blockNumber: lbn}) -> if (lbn >= cbn)
      then a
      else Map.insert idOracle {blockNumber: max (lbn + one) bn, value} a
    Just {blockNumber, value}, Nothing -> Map.insert idOracle {blockNumber: min blockNumber cbn, value} a
    Nothing, Just (OracleDataPoint {blockNumber, value}) -> if (blockNumber >= cbn)
      then a
      else Map.insert idOracle {blockNumber: cbn, value} a

  addOracle _ a = a

resizeSigs :: List Person -> Map Person Boolean -> Map Person Boolean
resizeSigs li ma = resizeSigsAux ma Map.empty li

updateChoices ::
  State ->
  Set IdInput ->
  Map Person (Map BigInteger Choice) ->
  Map Person (Map BigInteger Choice)
updateChoices (State state) inputs cmap = foldrDefault addChoice Map.empty inputs
  where
  addChoice (InputIdChoice (IdChoice {choice: idChoice, person})) a =
    let
      pmap = case Map.lookup person a of
        Nothing -> Map.empty
        Just y -> y
    in
      let
        dval = case Map.lookup person cmap of
          Nothing -> zero
          Just z -> case Map.lookup idChoice z of
            Nothing -> zero
            Just v -> v
      in
        if Map.member (WIdChoice (IdChoice {choice: idChoice, person})) state.choices
          then a
          else Map.insert person (Map.insert idChoice dval pmap) a

  addChoice _ a = a

resizeSigsAux ::
  Map Person Boolean ->
  Map Person Boolean ->
  List Person ->
  Map Person Boolean
resizeSigsAux ma ma2 Nil = ma2

resizeSigsAux ma ma2 (Cons x y) = case Map.lookup x ma of
  Just z -> resizeSigsAux ma (Map.insert x z ma2) y
  Nothing -> resizeSigsAux ma (Map.insert x false ma2) y

-- | Apply a function to the head of a non-empty list and cons the result on
extendWith :: forall a. (a -> a) -> NonEmptyList a -> NonEmptyList a
extendWith f l = NEL.cons ((f <<< NEL.head) l) l

emptyInputData :: InputData
emptyInputData =
  { inputs: Map.empty
  , choiceData: Map.empty
  , oracleData: Map.empty
  }

emptyTransactionData :: TransactionData
emptyTransactionData =
  { inputs: []
  , signatures: Map.empty
  , outcomes: Map.empty
  , validity: EmptyTransaction
  }

emptyMarloweState :: MarloweState
emptyMarloweState =
  { input: emptyInputData
  , transaction: emptyTransactionData
  , state: emptyState
  , blockNum: zero
  , moneyInContract: zero
  , contract: Nothing
  }
