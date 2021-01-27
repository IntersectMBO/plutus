module HaskellEditor.State
  ( handleAction
  , editorGetValue
  -- TODO: This should probably be exposed by an action
  , editorResize
  , editorSetTheme
  ) where

import Prelude hiding (div)
import BottomPanel.State (handleAction) as BottomPanel
import BottomPanel.Types (Action(..), State) as BottomPanel
import CloseAnalysis (analyseClose)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Array (catMaybes)
import Data.Either (Either(..), hush)
import Data.Foldable (for_)
import Data.Lens (assign, use)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Examples.Haskell.Contracts (example) as HE
import Halogen (HalogenM, liftEffect, query)
import Halogen.Extra (mapSubmodule)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import HaskellEditor.Types (Action(..), BottomPanelView(..), State, _bottomPanelState, _compilationResult, _haskellEditorKeybindings)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult(..))
import Language.Haskell.Monaco as HM
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _haskellEditorSlot)
import Marlowe (SPParams_, postRunghc)
import Marlowe.Holes (fromTerm)
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (Contract)
import Monaco (IMarkerData, markerSeverity)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticAnalysis.Reachability (analyseReachability)
import StaticAnalysis.StaticTools (analyseContract)
import StaticAnalysis.Types (AnalysisState(..), MultiStageAnalysisData(..), _analysisState)
import StaticData (haskellBufferLocalStorageKey)
import Types (WebData)
import Webghc.Server (CompileRequest(..))

toBottomPanel ::
  forall m a.
  Functor m =>
  HalogenM (BottomPanel.State BottomPanelView) (BottomPanel.Action BottomPanelView Action) ChildSlots Void m a ->
  HalogenM State Action ChildSlots Void m a
toBottomPanel = mapSubmodule _bottomPanelState BottomPanelAction

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction _ Init = do
  editorSetTheme
  mContents <- liftEffect $ LocalStorage.getItem haskellBufferLocalStorageKey
  editorSetValue $ fromMaybe HE.example mContents

handleAction _ (HandleEditorMessage (Monaco.TextChanged text)) = do
  liftEffect $ LocalStorage.setItem haskellBufferLocalStorageKey text
  assign _compilationResult NotAsked

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
      case result of
        Success (Left _) -> handleAction settings $ BottomPanelAction (BottomPanel.ChangePanel ErrorsView)
        _ -> pure unit
      let
        markers = case result of
          Success (Left errors) -> toMarkers errors
          _ -> []
      void $ query _haskellEditorSlot unit (Monaco.SetModelMarkers markers identity)

handleAction settings (BottomPanelAction (BottomPanel.PanelAction action)) = handleAction settings action

handleAction _ (BottomPanelAction action) = do
  toBottomPanel (BottomPanel.handleAction action)
  editorResize

handleAction _ SendResultToSimulator = pure unit

handleAction _ (InitHaskellProject contents) = do
  editorSetValue contents
  liftEffect $ LocalStorage.setItem haskellBufferLocalStorageKey contents

handleAction settings AnalyseContract = compileAndAnalyze settings (WarningAnalysis Loading) $ analyseContract settings

handleAction settings AnalyseReachabilityContract =
  compileAndAnalyze settings (ReachabilityAnalysis AnalysisNotStarted)
    $ analyseReachability settings

handleAction settings AnalyseContractForCloseRefund =
  compileAndAnalyze settings (CloseAnalysis AnalysisNotStarted)
    $ analyseClose settings

-- This function runs a static analysis to the compiled code. It calls the compiler if
-- it wasn't runned before and it switches to the error panel if the compilation failed
compileAndAnalyze ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  AnalysisState ->
  (Contract -> HalogenM State Action ChildSlots Void m Unit) ->
  HalogenM State Action ChildSlots Void m Unit
compileAndAnalyze settings initialAnalysisState doAnalyze = do
  compilationResult <- use _compilationResult
  case compilationResult of
    NotAsked -> do
      -- The initial analysis state allow us to show an "Analysing..." indicator
      assign _analysisState initialAnalysisState
      handleAction settings Compile
      compileAndAnalyze settings initialAnalysisState doAnalyze
    Success (Right (InterpreterResult interpretedResult)) ->
      let
        mContract = (fromTerm <=< hush <<< parseContract) interpretedResult.result
      in
        for_ mContract doAnalyze
    Success (Left _) -> handleAction settings $ BottomPanelAction $ BottomPanel.ChangePanel ErrorsView
    _ -> pure unit

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

editorSetTheme :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorSetTheme = void $ query _haskellEditorSlot unit (Monaco.SetTheme HM.daylightTheme.name unit)

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
