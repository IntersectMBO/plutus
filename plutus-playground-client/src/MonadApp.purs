module MonadApp where

import Prelude

import Ace (Annotation, Editor)
import Ace.EditSession as Session
import Ace.Editor as AceEditor
import Auth (AuthStatus)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except.Trans (ExceptT, runExceptT)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State.Class (class MonadState)
import Control.Monad.State.Trans (StateT)
import Control.Monad.Trans.Class (class MonadTrans, lift)
import Data.Maybe (Maybe(..))
import Data.MediaType (MediaType)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Json.JsonEither (JsonEither)
import Editor as Editor
import Effect (Effect)
import Effect.Aff (Milliseconds)
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import FileEvents as FileEvents
import Gist (Gist, GistId, NewGist)
import Halogen (HalogenM)
import Language.Haskell.Interpreter (InterpreterError, SourceCode(SourceCode), InterpreterResult)
import LocalStorage as LocalStorage
import Network.RemoteData as RemoteData
import Playground.Types (CompilationResult, Evaluation, EvaluationResult, PlaygroundError)
import Playground.Server (SPParams_)
import Playground.Server as Server
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (bufferLocalStorageKey)
import Types (ChildQuery, ChildSlot, EditorSlot(EditorSlot), Query, State, WebData, cpEditor)
import Web.HTML.Event.DataTransfer (DropEffect)
import Web.HTML.Event.DataTransfer as DataTransfer
import Web.HTML.Event.DragEvent (DragEvent, dataTransfer)

class
  Monad m <= MonadApp m where
  editorGetContents :: m (Maybe SourceCode)
  editorSetContents :: String -> Maybe Int -> m Unit
  editorSetAnnotations :: Array Annotation -> m Unit
  editorGotoLine :: Int -> Maybe Int -> m Unit
  --
  saveBuffer :: String -> m Unit
  preventDefault :: DragEvent -> m Unit
  setDropEffect :: DropEffect -> DragEvent -> m Unit
  setDataTransferData :: DragEvent -> MediaType -> String -> m Unit
  readFileFromDragEvent :: DragEvent -> m String
  --
  delay :: Milliseconds -> m Unit
  --
  getOauthStatus :: m (WebData AuthStatus)
  getGistByGistId :: GistId -> m (WebData Gist)
  postEvaluation :: Evaluation -> m (WebData (JsonEither PlaygroundError EvaluationResult))
  postGist :: NewGist -> m (WebData Gist)
  patchGistByGistId :: NewGist -> GistId -> m (WebData Gist)
  postContract :: SourceCode -> m (WebData (JsonEither InterpreterError (InterpreterResult CompilationResult)))

newtype HalogenApp m a
  = HalogenApp (HalogenM State Query ChildQuery ChildSlot Void m a)

derive instance newtypeHalogenApp :: Newtype (HalogenApp m a) _

derive newtype instance functorHalogenApp :: Functor (HalogenApp m)

derive newtype instance applicativeHalogenApp :: Applicative (HalogenApp m)

derive newtype instance applyHalogenApp :: Apply (HalogenApp m)

derive newtype instance bindHalogenApp :: Bind (HalogenApp m)

derive newtype instance monadHalogenApp :: Monad (HalogenApp m)

derive newtype instance monadTransHalogenApp :: MonadTrans HalogenApp

derive newtype instance monadStateHalogenApp :: MonadState State (HalogenApp m)

derive newtype instance monadAskHalogenApp :: MonadAsk env m => MonadAsk env (HalogenApp m)

instance monadThrowHalogenApp :: MonadThrow e m => MonadThrow e (HalogenApp m) where
  throwError e = lift (throwError e)

------------------------------------------------------------
runHalogenApp :: forall m a. HalogenApp m a -> HalogenM State Query ChildQuery ChildSlot Void m a
runHalogenApp = unwrap

instance monadAppHalogenApp ::
  ( MonadAsk (SPSettings_ SPParams_) m
  , MonadEffect m
  , MonadAff m
  ) =>
  MonadApp (HalogenApp m) where
  editorGetContents = map SourceCode <$> withEditor AceEditor.getValue
  editorSetContents contents cursor = void $ withEditor $ AceEditor.setValue contents cursor
  editorSetAnnotations annotations =
    void
      $ withEditor \editor -> do
          session <- AceEditor.getSession editor
          Session.setAnnotations annotations session
  editorGotoLine row column = void $ withEditor $ AceEditor.gotoLine row column (Just true)
  preventDefault event = wrap $ liftEffect $ FileEvents.preventDefault event
  setDropEffect dropEffect event = wrap $ liftEffect $ DataTransfer.setDropEffect dropEffect $ dataTransfer event
  setDataTransferData event mimeType value = wrap $ liftEffect $ DataTransfer.setData mimeType value $ dataTransfer event
  readFileFromDragEvent event = wrap $ liftAff $ FileEvents.readFileFromDragEvent event
  delay ms = wrap $ liftAff $ Aff.delay ms
  saveBuffer text = wrap $ liftEffect $ LocalStorage.setItem bufferLocalStorageKey text
  getOauthStatus = runAjax Server.getOauthStatus
  getGistByGistId gistId = runAjax $ Server.getGistsByGistId gistId
  postEvaluation evaluation = runAjax $ Server.postEvaluate evaluation
  postGist newGist = runAjax $ Server.postGists newGist
  patchGistByGistId newGist gistId = runAjax $ Server.patchGistsByGistId newGist gistId
  postContract source = runAjax $ Server.postContract source

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Query ChildQuery ChildSlot Void m) a ->
  HalogenApp m (WebData a)
runAjax action = wrap $ RemoteData.fromEither <$> runExceptT action

withEditor :: forall a m. MonadEffect m => (Editor -> Effect a) -> HalogenApp m (Maybe a)
withEditor = HalogenApp <<< Editor.withEditor cpEditor EditorSlot

instance monadAppState :: MonadApp m => MonadApp (StateT s m) where
   editorGetContents = lift editorGetContents
   editorSetContents contents cursor = lift $ editorSetContents contents cursor
   editorSetAnnotations annotations = lift $ editorSetAnnotations annotations
   editorGotoLine row column = lift $ editorGotoLine row column
   preventDefault event = lift $ preventDefault event
   setDropEffect dropEffect event = lift $ setDropEffect dropEffect event
   setDataTransferData event mimeType value = lift $ setDataTransferData event mimeType value
   readFileFromDragEvent event = lift $ readFileFromDragEvent event
   delay ms = lift $ delay ms
   saveBuffer text = lift $ saveBuffer text
   getOauthStatus = lift getOauthStatus
   getGistByGistId gistId = lift $ getGistByGistId gistId
   postEvaluation evaluation = lift $ postEvaluation evaluation
   postGist newGist = lift $ postGist newGist
   patchGistByGistId newGist gistId = lift $ patchGistByGistId newGist gistId
   postContract source = lift $ postContract source
