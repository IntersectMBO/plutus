module MainFrameTests
  ( all
  ) where

import Prelude
import Animation (class MonadAnimate)
import Auth (AuthRole(..), AuthStatus(..))
import Clipboard (class MonadClipboard)
import Control.Monad.Error.Extra (mapError)
import Control.Monad.Except (runExcept)
import Control.Monad.Except.Trans (class MonadThrow)
import Control.Monad.RWS.Trans (RWSResult(..), RWST(..), runRWST)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Control.Monad.State.Class (class MonadState, get)
import Cursor as Cursor
import Data.Either (Either(..))
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
import Editor.Types (State(..)) as Editor
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Foreign.Generic (decodeJSON)
import Gist (Gist, GistId, gistId)
import Gists.Types (GistAction(..))
import Halogen.Monaco (KeyBindings(..)) as Editor
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode(..))
import MainFrame (handleAction, mkInitialState)
import MonadApp (class MonadApp)
import Network.RemoteData (RemoteData(..), isNotAsked, isSuccess)
import Network.RemoteData as RemoteData
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Playground.Gists (playgroundGistFile)
import Playground.Server (SPParams_(..))
import Playground.Types (CompilationResult, ContractDemo, EvaluationResult)
import Servant.PureScript.Settings (SPSettings_, defaultSettings)
import StaticData (_contractDemoEditorContents, bufferLocalStorageKey, mkContractDemos)
import StaticData as StaticData
import Test.QuickCheck ((<?>))
import Test.Unit (TestSuite, failure, suite, test)
import Test.Unit.Assert (assert, equal, equal')
import Test.Unit.QuickCheck (quickCheck)
import Types (HAction(..), State, View(Editor, Simulations), WebData, _authStatus, _createGistResult, _currentView, _simulations)

all :: TestSuite
all =
  suite "MainFrame" do
    evalTests

------------------------------------------------------------
type World
  = { gists :: Map GistId Gist
    , editorContents :: Maybe SourceCode
    , localStorage :: Map String String
    , evaluationResult :: WebData EvaluationResult
    , compilationResult :: (WebData (Either InterpreterError (InterpreterResult CompilationResult)))
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
      pure editorContents
  editorSetContents contents cursor =
    MockApp
      $ assign (_1 <<< _editorContents) (Just contents)
  editorHandleAction _ = pure unit
  editorSetAnnotations annotations = pure unit
  --
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
  resizeEditor = pure unit
  resizeBalancesChart = pure unit
  scrollIntoView _ = pure unit

instance monadRecMockApp :: Monad m => MonadRec (MockApp m) where
  tailRecM step a = do
    v <- step a
    case v of
      Loop cont -> tailRecM step cont
      Done result -> pure result

-- | The mock app makes no attempt to animate anything, and just calls the embedded `action`.
instance monadAnimateMockApp :: MonadAnimate (MockApp m) State where
  animate toggle action = action

instance monadClipboardMockApp :: Monad m => MonadClipboard (MockApp m) where
  copy _ = pure unit

execMockApp :: forall m. MonadThrow Error m => World -> Array HAction -> m (Tuple World State)
execMockApp world queries = do
  initialState <-
    mkInitialState
      ( Editor.State
          { keyBindings: Editor.DefaultBindings
          , feedbackPaneMinimised: false
          , lastCompiledCode: Nothing
          , currentCodeIsCompiled: false
          , feedbackPaneDragStart: Nothing
          , feedbackPaneExtend: 0
          , feedbackPanePreviousExtend: 0
          }
      )
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
          result = execMockApp mockWorld [ ChangeView aView ]
        case result of
          Right (Tuple _ finalState) -> (aView == view _currentView finalState) <?> "Unexpected final view."
          Left err -> false <?> show err
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
      test "Gist loaded successfully" do
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
            equal
              2
              (Cursor.length (view _simulations finalState))
            case view playgroundGistFile gist of
              Nothing -> failure "Could not read gist content. Sample test data may be incorrect."
              Just sourceFile -> do
                equal' "Editor gets updated."
                  (Just (SourceCode sourceFile))
                  (view _editorContents finalWorld)
                equal' "Source gets stored."
                  (Just sourceFile)
                  (preview (_localStorage <<< ix (unwrap bufferLocalStorageKey)) finalWorld)
    test "Loading a script works." do
      Tuple finalWorld finalState <-
        ( execMockApp (set _editorContents Nothing mockWorld)
            [ LoadScript "Game" ]
        )
      contractDemos :: Array ContractDemo <- mapError (error <<< show) mkContractDemos
      equal' "Script gets loaded."
        (view _contractDemoEditorContents <$> StaticData.lookup "Game" contractDemos)
        finalWorld.editorContents
    test "Loading a script switches back to the editor." do
      loadCompilationResponse1
        >>= case _ of
            Left err -> failure err
            Right compilationResult -> do
              Tuple _ finalState <-
                execMockApp (mockWorld { compilationResult = compilationResult })
                  [ ChangeView Simulations
                  , LoadScript "Game"
                  ]
              equal' "View is reset." Editor $ view _currentView finalState

loadCompilationResponse1 ::
  forall m.
  MonadEffect m =>
  m (Either String (WebData (Either InterpreterError (InterpreterResult CompilationResult))))
loadCompilationResponse1 = do
  contents <- liftEffect $ FS.readTextFile UTF8 "generated/compilation_response.json"
  case runExcept $ decodeJSON contents of
    Left err -> pure $ Left $ show err
    Right value -> pure $ Right $ Success $ Right value
