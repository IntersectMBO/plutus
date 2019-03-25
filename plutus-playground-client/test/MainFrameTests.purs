module MainFrameTests
       ( all
       ) where

import Prelude

import AjaxUtils (decodeJson)
import Auth (AuthRole(..), AuthStatus(..))
import Control.Monad.Eff.Class (liftEff)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Control.Monad.Free (Free, foldFree, liftF)
import Control.Monad.RWS.Trans (RWSResult(..), RWST(..), runRWST)
import Control.Monad.Reader.Class (class MonadAsk, ask)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Control.Monad.State.Class (class MonadState, get)
import Cursor as Cursor
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Either (Either, fromRight)
import Data.Identity (Identity)
import Data.Lens (Lens', _1, assign, preview, set, use, view)
import Data.Lens.At (at)
import Data.Lens.Index (ix)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(Tuple))
import FileEvents (FILE)
import Gist (Gist, GistId, gistId)
import Language.Haskell.Interpreter (CompilationError, SourceCode(SourceCode), InterpreterError, InterpreterResult(InterpreterResult))
import MainFrame (eval, initialState)
import MonadApp (class MonadApp)
import Network.RemoteData (RemoteData(..), isNotAsked, isSuccess)
import Network.RemoteData as RemoteData
import Node.Encoding (Encoding(..))
import Node.FS (FS)
import Node.FS.Sync as FS
import Partial.Unsafe (unsafePartial)
import Playground.API (CompilationResult, EvaluationResult)
import Playground.Server (SPParams_(..))
import Servant.PureScript.Settings (SPSettings_, defaultSettings)
import StaticData (bufferLocalStorageKey)
import StaticData as StaticData
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (assert, equal')
import Test.Unit.QuickCheck (quickCheck)
import Types (Query(LoadScript, CompileProgram, LoadGist, SetGistUrl, ChangeView, CheckAuthStatus), State, View(..), WebData, _authStatus, _compilationResult, _createGistResult, _currentView, _evaluationResult, _simulations)

all :: forall aff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM, file :: FILE | aff)
all =
  suite "MainFrame" do
    evalTests

------------------------------------------------------------

type World =
  { gists :: Map GistId Gist
  , editorContents :: Maybe String
  , localStorage :: Map String String
  , evaluationResult :: WebData EvaluationResult
  , compilationResult :: (WebData (Either InterpreterError (InterpreterResult CompilationResult)))
  }

_gists :: forall r a. Lens' {gists :: a | r} a
_gists = prop (SProxy :: SProxy "gists")

_editorContents :: forall r a. Lens' {editorContents :: a | r} a
_editorContents = prop (SProxy :: SProxy "editorContents")

_localStorage :: forall r a. Lens' {localStorage :: a | r} a
_localStorage = prop (SProxy :: SProxy "localStorage")

-- | A dummy implementation of `MonadApp`, for testing the main eval loop.
newtype MockApp m a = MockApp (RWST (SPSettings_ SPParams_) Unit (Tuple World State) m a)

derive instance newtypeMockApp :: Newtype (MockApp m a) _

derive instance functorMockApp :: Functor m => Functor (MockApp m)

instance applicativeMockApp :: Monad m => Applicative (MockApp m) where
  pure v = wrap $ pure v

instance applyMockApp :: Monad m => Apply (MockApp m) where
  apply f v = wrap $ apply (unwrap f) (unwrap v)

instance bindMockApp :: Monad m => Bind (MockApp m) where
  bind m action = wrap $ do
    v <- unwrap m
    unwrap $ action v

instance monadMockApp :: Monad m => Monad (MockApp m)

instance monadStateMockApp :: Monad m => MonadState State (MockApp m) where
  state f = MockApp $ RWST \r (Tuple world appState) ->
    case f appState of
      (Tuple a appState') -> pure $ RWSResult (Tuple world appState') a unit

instance monadAskMockApp :: Monad m => MonadAsk (SPSettings_ SPParams_) (MockApp m) where
  ask = MockApp $ ask

instance monadAppMockApp :: Monad m => MonadApp (MockApp m) where
  editorGetContents = MockApp do
    editorContents <- use (_1 <<< _editorContents)
    pure $ SourceCode <$> editorContents

  editorSetContents contents cursor = MockApp $
    assign (_1 <<< _editorContents) (Just contents)

  editorSetAnnotations annotations = pure unit
  editorGotoLine row column = pure unit
  --
  saveBuffer contents = MockApp $
    assign (_1 <<< _localStorage <<< at (unwrap bufferLocalStorageKey)) (Just contents)

  preventDefault event = pure unit
  readFileFromDragEvent event = pure "TEST"
  updateChartsIfPossible = pure unit
  --
  getOauthStatus =
    pure $ Success $ AuthStatus { _authStatusAuthRole: GithubUser }

  getGistByGistId gistId = MockApp do
    Tuple {gists} _ <- get
    pure $ RemoteData.fromMaybe $ Map.lookup gistId gists

  postEvaluation evaluation = pure NotAsked

  postGist newGist = pure NotAsked
  patchGistByGistId newGist gistId = pure NotAsked
  postContract sourceCode = MockApp do
    Tuple {compilationResult} _ <- get
    pure compilationResult

instance monadRecMockApp :: Monad m => MonadRec (MockApp m) where
  tailRecM step a = do
    v <- step a
    case v of
      Loop cont -> tailRecM step cont
      Done result -> pure result

execMockApp :: forall m a. Monad m => World -> Free Query a -> m (Tuple World State)
execMockApp world query = do
  RWSResult state result writer <- runRWST
    (unwrap (foldFree eval query :: MockApp m a))
    (defaultSettings (SPParams_ {baseURL: "/"}))
    (Tuple world initialState)
  pure state

-- | Simulate dispatching a Query.
send :: forall f a. (Unit -> f a) -> Free f a
send f = liftF $ f unit

------------------------------------------------------------

mockWorld :: World
mockWorld =
  { gists: Map.empty
  , editorContents: Nothing
  , localStorage: Map.empty
  , compilationResult: NotAsked
  , evaluationResult: NotAsked
  }

evalTests :: forall aff. TestSuite (file :: FILE, fs :: FS, exception :: EXCEPTION, random :: RANDOM | aff)
evalTests =
  suite "eval" do

    test "CheckAuthStatus" do
      Tuple _ finalState <- execMockApp mockWorld $ send CheckAuthStatus
      assert "Auth Status loaded." $ isSuccess (view  _authStatus finalState)

    test "ChangeView" do
      quickCheck \aView -> do
        let Tuple _ finalState = unwrap (execMockApp mockWorld (send $ ChangeView aView) :: Identity (Tuple World State))
        aView == view _currentView finalState

    suite "LoadGist" do
      test "Bad URL" do
        Tuple _ finalState <- execMockApp mockWorld do
          send $ SetGistUrl "9cfe"
          send $ LoadGist
        assert "Gist not loaded." $ isNotAsked (view  _createGistResult finalState)

      test "Invalid URL" do
        Tuple _ finalState <- execMockApp mockWorld $ do
          send $ SetGistUrl "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
          send $ LoadGist
        assert "Gist not loaded." $ isNotAsked (view  _createGistResult finalState)

      test "Successfully" do
        contents <- liftEff $ FS.readTextFile UTF8 "test/gist1.json"
        let gist :: Gist
            gist = unsafePartial $ fromRight (jsonParser contents >>= decodeJson)
            steps = do
                send $ SetGistUrl (unwrap (view gistId gist))
                send $ LoadGist
        Tuple finalWorld finalState <- execMockApp
                                         (set (_gists <<< at (view gistId gist)) (Just gist) mockWorld)
                                         steps

        assert "Gist gets loaded." $ isSuccess (view  _createGistResult finalState)
        let sourceFile = unsafePartial $ fromJust $ Array.head (unwrap gist)._gistFiles >>= (unwrap >>> _._gistFileContent)
        equal' "Editor gets update."
          (Just sourceFile)
          (view _editorContents finalWorld)
        equal' "Source gets stored."
          (Just sourceFile)
          (preview (_localStorage <<< ix (unwrap bufferLocalStorageKey)) finalWorld)

    test "Loading a script works." do
        Tuple finalWorld finalState <- execMockApp (set _editorContents Nothing mockWorld) do
          send $ LoadScript "Game"
        equal' "Script gets loaded."
          (Map.lookup "Game" StaticData.demoFiles)
          finalWorld.editorContents

    test "Loading a script clears out some state." do
        contents <- liftEff $ FS.readTextFile UTF8 "test/compilation_response1.json"
        let compilationResult :: Either InterpreterError (InterpreterResult CompilationResult)
            compilationResult = unsafePartial $ fromRight (jsonParser contents >>= decodeJson)
        Tuple _ finalState <- execMockApp (mockWorld { compilationResult = Success compilationResult }) do
          send $ ChangeView Simulations
          send $ LoadScript "Game"
          send $ CompileProgram
        assert "Simulations are non-empty." $ not $ Cursor.null $ view _simulations finalState
        Tuple _ finalState <- execMockApp (mockWorld { compilationResult = Success compilationResult }) do
          send $ LoadScript "Game"
          send $ CompileProgram
          send $ LoadScript "Game"
        assert "Simulations are empty." $ Cursor.null $ view _simulations finalState
        assert "Evaluation is cleared." $ isNotAsked $ view _evaluationResult finalState
        assert "Compilation is cleared." $ isNotAsked $ view _compilationResult finalState
        equal' "View is reset." Editor $ view _currentView finalState
