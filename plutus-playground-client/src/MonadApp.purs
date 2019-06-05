module MonadApp where

import Prelude

import Ace (Annotation, Editor)
import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceQuery(..))
import Auth (AuthStatus)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except.Trans (ExceptT, runExceptT)
import Control.Monad.Reader.Class (class MonadAsk, ask)
import Control.Monad.State.Class (class MonadState, state)
import Control.Monad.Trans.Class (class MonadTrans, lift)
import Data.Maybe (Maybe(..))
import Data.MediaType (MediaType)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.RawJson (JsonEither)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import FileEvents as FileEvents
import Gist (Gist, GistId, NewGist)
import Halogen (HalogenM, query', request)
import Language.Haskell.Interpreter (InterpreterError, SourceCode(SourceCode), InterpreterResult)
import LocalStorage as LocalStorage
import Network.RemoteData as RemoteData
import Playground.API (CompilationResult, Evaluation, EvaluationResult)
import Playground.Server (SPParams_)
import Playground.Server as Server
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (bufferLocalStorageKey)
import Types (ChildQuery, ChildSlot, EditorSlot(EditorSlot), Query, State, WebData, cpEditor)
import Web.HTML.Event.DataTransfer (DropEffect)
import Web.HTML.Event.DataTransfer as DataTransfer
import Web.HTML.Event.DragEvent (DragEvent, dataTransfer)

class Monad m <= MonadApp m where
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
  getOauthStatus :: m (WebData AuthStatus)
  getGistByGistId :: GistId -> m (WebData Gist)
  postEvaluation :: Evaluation -> m (WebData EvaluationResult)
  postGist :: NewGist -> m (WebData Gist)
  patchGistByGistId :: NewGist -> GistId -> m (WebData Gist)
  postContract :: SourceCode -> m (WebData (JsonEither InterpreterError (InterpreterResult CompilationResult)))

newtype HalogenApp m a = HalogenApp (HalogenM State Query ChildQuery ChildSlot Void m a)

derive instance newtypeHalogenApp :: Newtype (HalogenApp m a) _

instance functorHalogenApp :: Functor m => Functor (HalogenApp m) where
  map f m = wrap $ map f $ unwrap m

instance applicativeHalogenApp :: Applicative m => Applicative (HalogenApp m) where
  pure v = wrap $ pure v

instance applyHalogenApp :: Apply m => Apply (HalogenApp m) where
  apply f v = wrap $ unwrap f <*> unwrap v

instance bindHalogenApp :: Bind m => Bind (HalogenApp m) where
  bind m action = wrap $ do
    v <- unwrap m
    unwrap $ action v

instance monadHalogenApp :: Monad m => Monad (HalogenApp m)

instance monadTransHalogenApp :: MonadTrans HalogenApp where
  lift = wrap <<< lift

instance monadStateApp :: Monad m => MonadState State (HalogenApp m) where
  state = wrap <<< state

instance monadAskHalogenApp :: MonadAsk env m => MonadAsk env (HalogenApp m) where
  ask = lift ask

instance monadThrowHalogenApp :: MonadThrow e m => MonadThrow e (HalogenApp m) where
  throwError e = lift (throwError e)

------------------------------------------------------------

runHalogenApp :: forall m a. HalogenApp m a -> HalogenM State Query ChildQuery ChildSlot Void m a
runHalogenApp = unwrap

instance monadAppHalogenApp ::
  ( MonadAsk (SPSettings_ SPParams_) m
  , MonadEffect m
  , MonadAff m
  )
  => MonadApp (HalogenApp m) where
  editorGetContents = map SourceCode <$> withEditor Editor.getValue
  editorSetContents contents cursor = void $ withEditor $ Editor.setValue contents cursor

  editorSetAnnotations annotations = void $ withEditor \editor -> do
      session <- Editor.getSession editor
      Session.setAnnotations annotations session

  editorGotoLine row column = void $ withEditor $ Editor.gotoLine row column (Just true)

  preventDefault event = wrap $ liftEffect $ FileEvents.preventDefault event

  setDropEffect dropEffect event = wrap $ liftEffect $ DataTransfer.setDropEffect dropEffect $ dataTransfer event
  setDataTransferData event mimeType value =
    wrap $ liftEffect $ DataTransfer.setData mimeType value $ dataTransfer event

  readFileFromDragEvent event = wrap $ liftAff $ FileEvents.readFileFromDragEvent event

  saveBuffer text = wrap $ liftEffect $ LocalStorage.setItem bufferLocalStorageKey text

  getOauthStatus = runAjax Server.getOauthStatus
  getGistByGistId gistId = runAjax $ Server.getGistsByGistId gistId
  postEvaluation evaluation = runAjax $ Server.postEvaluate evaluation
  postGist newGist = runAjax $ Server.postGists newGist
  patchGistByGistId newGist gistId = runAjax $ Server.patchGistsByGistId newGist gistId
  postContract source = runAjax $ Server.postContract source

runAjax :: forall m a.
  ExceptT AjaxError (HalogenM State Query ChildQuery ChildSlot Void m) a
  -> HalogenApp m (WebData a)
runAjax action = wrap $ RemoteData.fromEither <$> runExceptT action

withEditor :: forall a m. MonadEffect m => (Editor -> Effect a) -> HalogenApp m (Maybe a)
withEditor action = HalogenApp $ do
    mEditor <- query' cpEditor EditorSlot $ request GetEditor
    case join mEditor of
      Just editor -> Just <$> (liftEffect $ action editor)
      _ -> pure Nothing
