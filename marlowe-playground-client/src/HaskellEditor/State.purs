module HaskellEditor.State
  ( handleAction
  , editorGetValue
  -- TODO: This should probably be exposed by an action
  , editorResize
  ) where

import Prelude hiding (div)
import BottomPanel.State (handleAction) as BottomPanel
import BottomPanel.Types (Action(..), State) as BottomPanel
import Control.Monad.Except (ExceptT, lift, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (runMaybeT)
import Control.Monad.Reader (runReaderT)
import Data.Array (catMaybes)
import Data.Either (Either(..), hush)
import Data.Lens (assign, use)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, liftEffect, query)
import Halogen.Extra (mapSubmodule)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import HaskellEditor.Types (Action(..), BottomPanelView(..), State, _bottomPanelState, _compilationResult, _haskellEditorKeybindings)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult(..))
import Language.Haskell.Monaco as HM
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _haskellEditorSlot)
import Marlowe (SPParams_, postRunghc)
import Marlowe as Server
import Marlowe.Holes (fromTerm)
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (emptyState)
import Marlowe.Symbolic.Types.Request as MSReq
import Monaco (IMarkerData, markerSeverity)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticAnalysis.Types (AnalysisState(..), _analysisState)
import StaticData (bufferLocalStorageKey)
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
  mContents <- liftEffect $ LocalStorage.getItem bufferLocalStorageKey
  editorSetValue $ fromMaybe "" mContents

handleAction _ (HandleEditorMessage (Monaco.TextChanged text)) = do
  liftEffect $ LocalStorage.setItem bufferLocalStorageKey text
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
  liftEffect $ LocalStorage.setItem bufferLocalStorageKey contents

handleAction settings AnalyseContract = do
  compilationResult <- use _compilationResult
  case compilationResult of
    NotAsked -> do
      assign _analysisState (WarningAnalysis Loading)
      handleAction settings Compile
      handleAction settings AnalyseContract
    Success (Right (InterpreterResult interpretedResult)) -> analyseContract settings interpretedResult.result
    Success (Left _) -> handleAction settings $ BottomPanelAction $ BottomPanel.ChangePanel ErrorsView
    _ -> pure unit

-- FIXME: put in a more global place and refactor MarloweEditor handleAction to use this
analyseContract ::
  forall m state action slots.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  String ->
  HalogenM { analysisState :: AnalysisState | state } action slots Void m Unit
analyseContract settings contents =
  void
    $ runMaybeT do
        contract <- hoistMaybe $ parseContract' contents
        assign _analysisState (WarningAnalysis Loading)
        let
          emptySemanticState = emptyState zero
        response <- lift $ checkContractForWarnings contract emptySemanticState
        assign _analysisState (WarningAnalysis response)
  where
  parseContract' = fromTerm <=< hush <<< parseContract

  checkContractForWarnings contract state = runAjax' $ (flip runReaderT) settings (Server.postMarloweanalysis (MSReq.Request { onlyAssertions: false, contract, state }))

  runAjax' action = RemoteData.fromEither <$> runExceptT action

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
