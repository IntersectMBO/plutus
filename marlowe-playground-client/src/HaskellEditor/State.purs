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
import Control.Monad.Reader (class MonadAsk, asks, runReaderT)
import Data.Array (catMaybes)
import Data.Either (Either(..), hush)
import Data.Foldable (for_)
import Data.Lens (assign, modifying, use)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Examples.Haskell.Contracts (example) as HE
import Halogen (HalogenM, liftEffect, query)
import Halogen.Extra (mapSubmodule)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import HaskellEditor.Types (Action(..), BottomPanelView(..), State, _bottomPanelState, _compilationResult, _haskellEditorKeybindings)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult(..))
import Language.Haskell.Monaco as HM
import MainFrame.Types (ChildSlots, _haskellEditorSlot)
import Marlowe (postRunghc)
import Marlowe.Extended (Contract, getPlaceholderIds, typeToLens, updateTemplateContent)
import Marlowe.Holes (fromTerm)
import Marlowe.Parser (parseContract)
import Monaco (IMarkerData, markerSeverity)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import SessionStorage as SessionStorage
import StaticAnalysis.Reachability (analyseReachability)
import StaticAnalysis.StaticTools (analyseContract)
import StaticAnalysis.Types (AnalysisExecutionState(..), MultiStageAnalysisData(..), _analysisExecutionState, _analysisState, _templateContent)
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
  MonadAsk Env m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction Init = do
  editorSetTheme
  mContents <- liftEffect $ SessionStorage.getItem haskellBufferLocalStorageKey
  editorSetValue $ fromMaybe HE.example mContents

handleAction (HandleEditorMessage (Monaco.TextChanged text)) = do
  liftEffect $ SessionStorage.setItem haskellBufferLocalStorageKey text
  assign _compilationResult NotAsked

handleAction (ChangeKeyBindings bindings) = do
  assign _haskellEditorKeybindings bindings
  void $ query _haskellEditorSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction Compile = do
  settings <- asks _.ajaxSettings
  mContents <- editorGetValue
  case mContents of
    Nothing -> pure unit
    Just code -> do
      assign _compilationResult Loading
      result <- runAjax $ flip runReaderT settings $ postRunghc (CompileRequest { code, implicitPrelude: true })
      assign _compilationResult result
      -- Update the error display.
      case result of
        Success (Left _) -> handleAction $ BottomPanelAction (BottomPanel.ChangePanel ErrorsView)
        Success (Right (InterpreterResult interpretedResult)) ->
          let
            mContract :: Maybe Contract
            mContract = (fromTerm <=< hush <<< parseContract) interpretedResult.result
          in
            for_ mContract $ (modifying (_analysisState <<< _templateContent)) <<< updateTemplateContent <<< getPlaceholderIds
        _ -> pure unit
      let
        markers = case result of
          Success (Left errors) -> toMarkers errors
          _ -> []
      void $ query _haskellEditorSlot unit (Monaco.SetModelMarkers markers identity)

handleAction (BottomPanelAction (BottomPanel.PanelAction action)) = handleAction action

handleAction (BottomPanelAction action) = do
  toBottomPanel (BottomPanel.handleAction action)
  editorResize

handleAction SendResultToSimulator = pure unit

handleAction (InitHaskellProject contents) = do
  editorSetValue contents
  liftEffect $ SessionStorage.setItem haskellBufferLocalStorageKey contents

handleAction (SetIntegerTemplateParam templateType key value) = modifying (_analysisState <<< _templateContent <<< typeToLens templateType) (Map.insert key value)

handleAction AnalyseContract = analyze (WarningAnalysis Loading) $ analyseContract

handleAction AnalyseReachabilityContract =
  analyze (ReachabilityAnalysis AnalysisNotStarted)
    $ analyseReachability

handleAction AnalyseContractForCloseRefund =
  analyze (CloseAnalysis AnalysisNotStarted)
    $ analyseClose

handleAction ClearAnalysisResults = assign (_analysisState <<< _analysisExecutionState) NoneAsked

-- This function runs a static analysis to the compiled code if it compiled successfully.
analyze ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  AnalysisExecutionState ->
  (Contract -> HalogenM State Action ChildSlots Void m Unit) ->
  HalogenM State Action ChildSlots Void m Unit
analyze initialAnalysisState doAnalyze = do
  compilationResult <- use _compilationResult
  case compilationResult of
    Success (Right (InterpreterResult interpretedResult)) ->
      let
        mContract = (fromTerm <=< hush <<< parseContract) interpretedResult.result
      in
        for_ mContract doAnalyze
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
