module MonadApp where

import Prelude
import Animation (class MonadAnimate, animate)
import Auth (AuthStatus)
import Clipboard (class MonadClipboard, copy)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except.Trans (ExceptT, runExceptT)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State.Class (class MonadState)
import Control.Monad.State.Trans (StateT)
import Control.Monad.Trans.Class (class MonadTrans, lift)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Data.MediaType (MediaType)
import Data.Newtype (class Newtype, unwrap, wrap)
import Editor.State (handleAction, saveBuffer) as Editor
import Editor.Types (Action) as Editor
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import FileEvents as FileEvents
import Gist (Gist, GistId, NewGist)
import Halogen (HalogenM, RefLabel, query, tell)
import Halogen as H
import Halogen.Chartist as Chartist
import Halogen.Extra as HE
import Halogen.Monaco as Monaco
import Language.Haskell.Interpreter (InterpreterError, SourceCode(SourceCode), InterpreterResult)
import Monaco (IMarkerData)
import Network.RemoteData as RemoteData
import Playground.Server (SPParams_)
import Playground.Server as Server
import Playground.Types (CompilationResult, Evaluation, EvaluationResult, PlaygroundError)
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (bufferLocalStorageKey)
import Types (ChildSlots, HAction, State, WebData, _balancesChartSlot, _editorSlot, _editorState)
import Web.HTML.Event.DataTransfer (DropEffect)
import Web.HTML.Event.DataTransfer as DataTransfer
import Web.HTML.Event.DragEvent (DragEvent, dataTransfer)

class
  Monad m <= MonadApp m where
  editorGetContents :: m (Maybe SourceCode)
  editorSetContents :: SourceCode -> Maybe Int -> m Unit
  editorHandleAction :: Editor.Action -> m Unit
  editorSetAnnotations :: Array IMarkerData -> m Unit
  --
  saveBuffer :: String -> m Unit
  preventDefault :: DragEvent -> m Unit
  setDropEffect :: DropEffect -> DragEvent -> m Unit
  setDataTransferData :: DragEvent -> MediaType -> String -> m Unit
  readFileFromDragEvent :: DragEvent -> m String
  --
  getOauthStatus :: m (WebData AuthStatus)
  getGistByGistId :: GistId -> m (WebData Gist)
  postEvaluation :: Evaluation -> m (WebData (Either PlaygroundError EvaluationResult))
  postGist :: NewGist -> m (WebData Gist)
  patchGistByGistId :: NewGist -> GistId -> m (WebData Gist)
  postContract :: SourceCode -> m (WebData (Either InterpreterError (InterpreterResult CompilationResult)))
  resizeEditor :: m Unit
  resizeBalancesChart :: m Unit
  scrollIntoView :: RefLabel -> m Unit

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

instance monadClipboardHalogenApp :: MonadEffect m => MonadClipboard (HalogenApp m) where
  copy = liftEffect <<< copy

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
  editorGetContents = do
    mText <- wrap $ query _editorSlot unit $ Monaco.GetText identity
    pure $ map SourceCode mText
  editorSetContents (SourceCode contents) cursor = wrap $ void $ query _editorSlot unit $ tell $ Monaco.SetText contents
  editorHandleAction action = wrap $ HE.imapState _editorState $ Editor.handleAction bufferLocalStorageKey action
  editorSetAnnotations annotations = wrap $ void $ query _editorSlot unit $ Monaco.SetModelMarkers annotations identity
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
  resizeEditor = wrap $ void $ H.query _editorSlot unit (Monaco.Resize unit)
  resizeBalancesChart = wrap $ void $ H.query _balancesChartSlot unit (Chartist.Resize unit)
  scrollIntoView ref = wrap $ HE.scrollIntoView ref

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State HAction ChildSlots Void m) a ->
  HalogenApp m (WebData a)
runAjax action = wrap $ RemoteData.fromEither <$> runExceptT action

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
  resizeEditor = lift resizeEditor
  resizeBalancesChart = lift resizeBalancesChart
  scrollIntoView = lift <<< scrollIntoView
