module MainFrameTests
  ( all
  ) where

import Prelude
import Auth (AuthRole(..), AuthStatus(..))
import Control.Monad.Except (runExcept)
import Control.Monad.RWS.Trans (RWSResult(..), RWST(..), runRWST)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Control.Monad.State.Class (class MonadState, get)
import Cursor as Cursor
import Data.Array as Array
import Data.Either (Either(Right, Left))
import Data.Identity (Identity)
import Data.Json.JsonEither (JsonEither)
import Data.Lens (Lens', _1, assign, preview, set, use, view)
import Data.Lens.At (at)
import Data.Lens.Index (ix)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Nothing, Just))
import Data.Newtype (class Newtype, unwrap)
import Data.Symbol (SProxy(..))
import Data.Traversable (traverse_)
import Data.Tuple (Tuple(Tuple))
import Editor (EditorAction(..))
import Effect.Class (class MonadEffect, liftEffect)
import Foreign.Generic (decodeJSON)
import Gist (Gist, GistId, gistId)
import Gists (GistAction(..))
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode(SourceCode))
import MainFrame (handleAction, initialState)
import MonadApp (class MonadApp)
import Network.RemoteData (RemoteData(..), isNotAsked, isSuccess)
import Network.RemoteData as RemoteData
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Playground.Server (SPParams_(..))
import Playground.Types (CompilationResult, EvaluationResult)
import Servant.PureScript.Settings (SPSettings_, defaultSettings)
import StaticData (bufferLocalStorageKey)
import StaticData as StaticData
import Test.Unit (TestSuite, failure, suite, test)
import Test.Unit.Assert (assert, equal')
import Test.Unit.QuickCheck (quickCheck)
import Types (HAction(..), State, View(Editor, Simulations), WebData, _authStatus, _compilationResult, _createGistResult, _currentView, _evaluationResult, _simulations)

all :: TestSuite
all =
  suite "MainFrame" do
    evalTests

------------------------------------------------------------
type World
  = { gists :: Map GistId Gist
    , editorContents :: Maybe String
    , localStorage :: Map String String
    , evaluationResult :: WebData EvaluationResult
    , compilationResult :: (WebData (JsonEither InterpreterError (InterpreterResult CompilationResult)))
    }

_gists :: forall r a. Lens' { gists :: a | r } a
_gists = prop (SProxy :: SProxy "gists")

_editorContents :: forall r a. Lens' { editorContents :: a | r } a
_editorContents = prop (SProxy :: SProxy "editorContents")

_localStorage :: forall r a. Lens' { localStorage :: a | r } a
_localStorage = prop (SProxy :: SProxy "localStorage")

-- | A dummy implementation of `MonadApp`, for testing the main handleAction loop.
newtype MockApp m a
  = MockApp (RWST (SPSettings_ SPParams_) Unit (Tuple World State) m a)

derive instance newtypeMockApp :: Newtype (MockApp m a) _

derive newtype instance functorMockApp :: Functor m => Functor (MockApp m)

derive newtype instance applicativeMockApp :: Monad m => Applicative (MockApp m)

derive newtype instance applyMockApp :: Bind m => Apply (MockApp m)

derive newtype instance bindMockApp :: Bind m => Bind (MockApp m)

derive newtype instance monadMockApp :: Monad m => Monad (MockApp m)

derive newtype instance monadAskMockApp :: Monad m => MonadAsk (SPSettings_ SPParams_) (MockApp m)

instance monadStateMockApp :: Monad m => MonadState State (MockApp m) where
  state f =
    MockApp
      $ RWST \r (Tuple world appState) -> case f appState of
          (Tuple a appState') -> pure $ RWSResult (Tuple world appState') a unit

instance monadAppMockApp :: Monad m => MonadApp (MockApp m) where
  editorGetContents =
    MockApp do
      editorContents <- use (_1 <<< _editorContents)
      pure $ SourceCode <$> editorContents
  editorSetContents contents cursor =
    MockApp
      $ assign (_1 <<< _editorContents) (Just contents)
  editorSetAnnotations annotations = pure unit
  editorGotoLine row column = pure unit
  --
  delay time = pure unit
  saveBuffer contents =
    MockApp
      $ assign (_1 <<< _localStorage <<< at (unwrap bufferLocalStorageKey)) (Just contents)
  preventDefault event = pure unit
  setDropEffect effectType event = pure unit
  setDataTransferData event mimeType value = pure unit
  readFileFromDragEvent event = pure "TEST"
  --
  getOauthStatus = pure $ Success $ AuthStatus { _authStatusAuthRole: GithubUser }
  getGistByGistId gistId =
    MockApp do
      Tuple { gists } _ <- get
      pure $ RemoteData.fromMaybe $ Map.lookup gistId gists
  postEvaluation evaluation = pure NotAsked
  postGist newGist = pure NotAsked
  patchGistByGistId newGist gistId = pure NotAsked
  postContract sourceCode =
    MockApp do
      Tuple { compilationResult } _ <- get
      pure compilationResult

instance monadRecMockApp :: Monad m => MonadRec (MockApp m) where
  tailRecM step a = do
    v <- step a
    case v of
      Loop cont -> tailRecM step cont
      Done result -> pure result

execMockApp :: forall m. Monad m => World -> Array HAction -> m (Tuple World State)
execMockApp world queries = do
  RWSResult state result writer <-
    runRWST
      (unwrap (traverse_ handleAction queries :: MockApp m Unit))
      (defaultSettings (SPParams_ { baseURL: "/" }))
      (Tuple world initialState)
  pure state

------------------------------------------------------------
mockWorld :: World
mockWorld =
  { gists: Map.empty
  , editorContents: Nothing
  , localStorage: Map.empty
  , compilationResult: NotAsked
  , evaluationResult: NotAsked
  }

evalTests :: TestSuite
evalTests =
  suite "handleAction" do
    test "CheckAuthStatus" do
      Tuple _ finalState <- execMockApp mockWorld [ CheckAuthStatus ]
      assert "Auth Status loaded." $ isSuccess (view _authStatus finalState)
    test "ChangeView" do
      quickCheck \aView -> do
        let
          Tuple _ finalState = unwrap (execMockApp mockWorld [ ChangeView aView ] :: Identity (Tuple World State))
        aView == view _currentView finalState
    suite "LoadGist" do
      test "Bad URL" do
        Tuple _ finalState <-
          execMockApp mockWorld
            [ GistAction $ SetGistUrl "9cfe"
            , GistAction LoadGist
            ]
        assert "Gist not loaded." $ isNotAsked (view _createGistResult finalState)
      test "Invalid URL" do
        Tuple _ finalState <-
          execMockApp mockWorld
            [ GistAction $ SetGistUrl "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
            , GistAction LoadGist
            ]
        assert "Gist not loaded." $ isNotAsked (view _createGistResult finalState)
      test "Successfully" do
        contents <- liftEffect $ FS.readTextFile UTF8 "test/gist1.json"
        case runExcept $ decodeJSON contents of
          Left err -> failure $ show err
          Right gist -> do
            Tuple finalWorld finalState <-
              execMockApp
                (set (_gists <<< at (view gistId gist)) (Just gist) mockWorld)
                [ GistAction $ SetGistUrl (unwrap (view gistId gist))
                , GistAction LoadGist
                ]
            assert "Gist gets loaded." $ isSuccess (view _createGistResult finalState)
            equal'
              "Simulation gets loaded."
              1
              (Cursor.length (view _simulations finalState))
            case Array.head (unwrap gist)._gistFiles >>= (unwrap >>> _._gistFileContent) of
              Nothing -> failure "Could not read gist content. Sample test data may be incorrect."
              Just sourceFile -> do
                equal' "Editor gets update."
                  (Just sourceFile)
                  (view _editorContents finalWorld)
                equal' "Source gets stored."
                  (Just sourceFile)
                  (preview (_localStorage <<< ix (unwrap bufferLocalStorageKey)) finalWorld)
    test "Loading a script works." do
      Tuple finalWorld finalState <-
        execMockApp (set _editorContents Nothing mockWorld)
          [ EditorAction $ LoadScript "Game" ]
      equal' "Script gets loaded."
        (Map.lookup "Game" StaticData.demoFiles)
        finalWorld.editorContents
    test "Loading a script clears out some state." do
      loadCompilationResponse1
        >>= case _ of
            Left err -> failure err
            Right compilationResult -> do
              Tuple _ intermediateState <-
                execMockApp (mockWorld { compilationResult = compilationResult })
                  [ ChangeView Simulations
                  , EditorAction $ LoadScript "Game"
                  , EditorAction CompileProgram
                  ]
              assert "Simulations are non-empty." $ not $ Cursor.null $ view _simulations intermediateState
              Tuple _ finalState <-
                execMockApp (mockWorld { compilationResult = compilationResult })
                  [ EditorAction $ LoadScript "Game"
                  , EditorAction CompileProgram
                  , EditorAction $ LoadScript "Game"
                  ]
              assert "Simulations are empty." $ Cursor.null $ view _simulations finalState
              assert "Evaluation is cleared." $ isNotAsked $ view _evaluationResult finalState
              assert "Compilation is cleared." $ isNotAsked $ view _compilationResult finalState
    test "Loading a script switches back to the editor." do
      loadCompilationResponse1
        >>= case _ of
            Left err -> failure err
            Right compilationResult -> do
              Tuple _ finalState <-
                execMockApp (mockWorld { compilationResult = compilationResult })
                  [ ChangeView Simulations
                  , EditorAction $ LoadScript "Game"
                  ]
              equal' "View is reset." Editor $ view _currentView finalState

loadCompilationResponse1 ::
  forall m.
  MonadEffect m =>
  m (Either String (WebData (JsonEither InterpreterError (InterpreterResult CompilationResult))))
loadCompilationResponse1 = do
  contents <- liftEffect $ FS.readTextFile UTF8 "test/compilation_response1.json"
  case runExcept $ decodeJSON contents of
    Left err -> pure $ Left $ show err
    Right value -> pure $ Right $ Success value
