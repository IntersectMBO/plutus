module MonadApp where

import Prelude
import Ace (Annotation, Editor)
import Ace.EditSession as Session
import Ace.Editor as AceEditor
import Animation (class MonadAnimate, animate)
import Auth (AuthStatus)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except.Trans (ExceptT, runExceptT)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State.Class (class MonadState)
import Control.Monad.State.Trans (StateT)
import Control.Monad.Trans.Class (class MonadTrans, lift)
import Data.Json.JsonEither (JsonEither)
import Data.Maybe (Maybe)
import Data.MediaType (MediaType)
import Data.Newtype (class Newtype, unwrap, wrap)
import Editor as Editor
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import FileEvents as FileEvents
import Gist (Gist, GistId, NewGist)
import Halogen (HalogenM)
import Halogen as H
import Halogen.Chartist as Chartist
import Language.Haskell.Interpreter (InterpreterError, SourceCode(SourceCode), InterpreterResult)
import Network.RemoteData as RemoteData
import Playground.Server (SPParams_)
import Playground.Server as Server
import Playground.Types (CompilationResult, Evaluation, EvaluationResult, PlaygroundError)
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (bufferLocalStorageKey)
import Types (ChildSlots, HAction, State, WebData, _balancesChartSlot, _editorSlot)
import Web.HTML.Event.DataTransfer (DropEffect)
import Web.HTML.Event.DataTransfer as DataTransfer
import Web.HTML.Event.DragEvent (DragEvent, dataTransfer)

class
  Monad m <= MonadApp m where
  editorGetContents :: m (Maybe SourceCode)
  editorSetContents :: SourceCode -> Maybe Int -> m Unit
  editorHandleAction :: Editor.Action -> m Unit
  editorSetAnnotations :: Array Annotation -> m Unit
  --
  saveBuffer :: String -> m Unit
  preventDefault :: DragEvent -> m Unit
  setDropEffect :: DropEffect -> DragEvent -> m Unit
  setDataTransferData :: DragEvent -> MediaType -> String -> m Unit
  readFileFromDragEvent :: DragEvent -> m String
  --
  getOauthStatus :: m (WebData AuthStatus)
  getGistByGistId :: GistId -> m (WebData Gist)
  postEvaluation :: Evaluation -> m (WebData (JsonEither PlaygroundError EvaluationResult))
  postGist :: NewGist -> m (WebData Gist)
  patchGistByGistId :: NewGist -> GistId -> m (WebData Gist)
  postContract :: SourceCode -> m (WebData (JsonEither InterpreterError (InterpreterResult CompilationResult)))
  resizeBalancesChart :: m Unit

newtype HalogenApp m a
  = HalogenApp (HalogenM State HAction ChildSlots Void m a)

derive instance newtypeHalogenApp :: Newtype (HalogenApp m a) _

derive newtype instance functorHalogenApp :: Functor (HalogenApp m)

derive newtype instance applicativeHalogenApp :: Applicative (HalogenApp m)

derive newtype instance applyHalogenApp :: Apply (HalogenApp m)

derive newtype instance bindHalogenApp :: Bind (HalogenApp m)

derive newtype instance monadHalogenApp :: Monad (HalogenApp m)

derive newtype instance monadTransHalogenApp :: MonadTrans HalogenApp

derive newtype instance monadStateHalogenApp :: MonadState State (HalogenApp m)

derive newtype instance monadAskHalogenApp :: MonadAsk env m => MonadAsk env (HalogenApp m)

derive newtype instance monadEffectHalogenApp :: MonadEffect m => MonadEffect (HalogenApp m)

derive newtype instance monadAffHalogenApp :: MonadAff m => MonadAff (HalogenApp m)

instance monadAnimateHalogenApp :: MonadAff m => MonadAnimate (HalogenApp m) State where
  animate toggle action = HalogenApp $ animate toggle (unwrap action)

instance monadThrowHalogenApp :: MonadThrow e m => MonadThrow e (HalogenApp m) where
  throwError e = lift (throwError e)

------------------------------------------------------------
runHalogenApp :: forall m a. HalogenApp m a -> HalogenM State HAction ChildSlots Void m a
runHalogenApp = unwrap

instance monadAppHalogenApp ::
  ( MonadAsk (SPSettings_ SPParams_) m
  , MonadEffect m
  , MonadAff m
  ) =>
  MonadApp (HalogenApp m) where
  editorGetContents = map SourceCode <$> withEditor (liftEffect <<< AceEditor.getValue)
  editorSetContents (SourceCode contents) cursor = void $ withEditor $ liftEffect <<< AceEditor.setValue contents cursor
  editorHandleAction action = void $ withEditor $ Editor.handleAction bufferLocalStorageKey action
  editorSetAnnotations annotations =
    void
      $ withEditor \editor ->
          liftEffect do
            session <- AceEditor.getSession editor
            Session.setAnnotations annotations session
  preventDefault event = wrap $ liftEffect $ FileEvents.preventDefault event
  setDropEffect dropEffect event = wrap $ liftEffect $ DataTransfer.setDropEffect dropEffect $ dataTransfer event
  setDataTransferData event mimeType value = wrap $ liftEffect $ DataTransfer.setData mimeType value $ dataTransfer event
  readFileFromDragEvent event = wrap $ liftAff $ FileEvents.readFileFromDragEvent event
  saveBuffer text = wrap $ Editor.saveBuffer bufferLocalStorageKey text
  getOauthStatus = runAjax Server.getOauthStatus
  getGistByGistId gistId = runAjax $ Server.getGistsByGistId gistId
  postEvaluation evaluation = runAjax $ Server.postEvaluate evaluation
  postGist newGist = runAjax $ Server.postGists newGist
  patchGistByGistId newGist gistId = runAjax $ Server.patchGistsByGistId newGist gistId
  postContract source = runAjax $ Server.postContract source
  resizeBalancesChart = wrap $ void $ H.query _balancesChartSlot unit (Chartist.Resize unit)

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State HAction ChildSlots Void m) a ->
  HalogenApp m (WebData a)
runAjax action = wrap $ RemoteData.fromEither <$> runExceptT action

withEditor :: forall a m. MonadEffect m => (Editor -> m a) -> HalogenApp m (Maybe a)
withEditor = HalogenApp <<< Editor.withEditor _editorSlot unit

instance monadAppState :: MonadApp m => MonadApp (StateT s m) where
  editorGetContents = lift editorGetContents
  editorSetContents contents cursor = lift $ editorSetContents contents cursor
  editorHandleAction action = lift $ editorHandleAction action
  editorSetAnnotations annotations = lift $ editorSetAnnotations annotations
  preventDefault event = lift $ preventDefault event
  setDropEffect dropEffect event = lift $ setDropEffect dropEffect event
  setDataTransferData event mimeType value = lift $ setDataTransferData event mimeType value
  readFileFromDragEvent event = lift $ readFileFromDragEvent event
  saveBuffer text = lift $ saveBuffer text
  getOauthStatus = lift getOauthStatus
  getGistByGistId gistId = lift $ getGistByGistId gistId
  postEvaluation evaluation = lift $ postEvaluation evaluation
  postGist newGist = lift $ postGist newGist
  patchGistByGistId newGist gistId = lift $ patchGistByGistId newGist gistId
  postContract source = lift $ postContract source
  resizeBalancesChart = lift resizeBalancesChart
