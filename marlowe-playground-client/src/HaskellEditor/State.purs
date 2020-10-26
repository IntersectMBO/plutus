module HaskellEditor.State where

import Prelude hiding (div)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Array (catMaybes)
import Data.Either (Either(..))
import Data.Lens (assign, use, view)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, liftEffect, query)
import Halogen.Blockly as Blockly
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import HaskellEditor.Types (Action(..), State, _activeHaskellDemo, _compilationResult, _haskellEditorKeybindings, _showBottomPanel)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), _InterpreterResult)
import LocalStorage as LocalStorage
import Marlowe (SPParams_, postRunghc)
import Monaco (IMarkerData, markerSeverity)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import Simulation.State (_result)
import Simulation.Types (WebData)
import StaticData (bufferLocalStorageKey)
import StaticData as StaticData
import MainFrame.Types (ChildSlots, _blocklySlot, _haskellEditorSlot)
import Webghc.Server (CompileRequest(..))

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction _ (HandleEditorMessage (Monaco.TextChanged text)) = do
  liftEffect $ LocalStorage.setItem bufferLocalStorageKey text
  assign _compilationResult NotAsked
  assign _activeHaskellDemo ""

handleAction _ (ChangeKeyBindings bindings) = do
  assign _haskellEditorKeybindings bindings
  void $ query _haskellEditorSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction settings Compile = do
  mContents <- editorGetValue
  case mContents of
    Nothing -> pure unit
    Just code -> do
      assign _compilationResult Loading
      result <- runAjax $ flip runReaderT settings $ postRunghc (CompileRequest { code, implicitPrelude: true })
      assign _compilationResult result
      -- Update the error display.
      let
        markers = case result of
          Success (Left errors) -> toMarkers errors
          _ -> []
      void $ query _haskellEditorSlot unit (Monaco.SetModelMarkers markers identity)

handleAction _ (LoadScript key) = do
  case Map.lookup key StaticData.demoFiles of
    Nothing -> pure unit
    Just contents -> do
      editorSetValue contents
      assign _activeHaskellDemo key

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  editorResize

handleAction _ SendResultToSimulator = pure unit

handleAction _ SendResultToBlockly = do
  mContract <- use _compilationResult
  case mContract of
    Success (Right result) -> do
      let
        source = view (_InterpreterResult <<< _result) result
      void $ query _blocklySlot unit (Blockly.SetCode source unit)
    _ -> pure unit

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

editorResize :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorResize = void $ query _haskellEditorSlot unit (Monaco.Resize unit)

editorSetValue :: forall state action msg m. String -> HalogenM state action ChildSlots msg m Unit
editorSetValue contents = void $ query _haskellEditorSlot unit (Monaco.SetText contents unit)

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _haskellEditorSlot unit (Monaco.GetText identity)

toMarkers :: InterpreterError -> Array IMarkerData
toMarkers (TimeoutError _) = []

toMarkers (CompilationErrors errors) = catMaybes (toMarker <$> errors)

toMarker :: CompilationError -> Maybe IMarkerData
toMarker (RawError _) = Nothing

toMarker (CompilationError { row, column, text }) =
  Just
    { severity: markerSeverity "Error"
    , message: String.joinWith "\\n" text
    , startLineNumber: row
    , startColumn: column
    , endLineNumber: row
    , endColumn: column
    , code: mempty
    , source: mempty
    }
