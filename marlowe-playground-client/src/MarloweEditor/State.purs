module MarloweEditor.State
  ( handleAction
  , editorGetValue
  , {- FIXME: this should be an action -} editorResize
  ) where

import Prelude hiding (div)
import BottomPanel.State (handleAction) as BottomPanel
import BottomPanel.Types (Action(..), State) as BottomPanel
import CloseAnalysis (startCloseAnalysis)
import Control.Monad.Except (ExceptT, lift, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Data.Array (filter)
import Data.Either (Either(..), hush)
import Data.Foldable (for_, traverse_)
import Data.Lens (assign, preview, set, use)
import Data.Lens.Index (ix)
import Data.Maybe (Maybe(..))
import Data.String (codePointFromChar)
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Halogen (HalogenM, liftEffect, modify_, query)
import Halogen.Extra (mapSubmodule)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _marloweEditorPageSlot)
import Marlowe (SPParams_)
import Marlowe.Holes (fromTerm)
import Marlowe.Linter as Linter
import Marlowe.Monaco (updateAdditionalContext)
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (Contract, emptyState)
import MarloweEditor.Types (Action(..), BottomPanelView, State, _bottomPanelState, _editorErrors, _editorWarnings, _keybindings, _selectedHole, _showErrorDetail)
import Monaco (IMarker, isError, isWarning)
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticAnalysis.Reachability (analyseReachability, getUnreachableContracts, startReachabilityAnalysis)
import StaticAnalysis.StaticTools (analyseContract)
import StaticAnalysis.Types (AnalysisState(..), _analysisState)
import StaticData (marloweBufferLocalStorageKey)
import StaticData as StaticData
import Text.Pretty (pretty)
import Types (WebData)
import Web.Event.Extra (preventDefault, readFileFromDragEvent)

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
handleAction _ (ChangeKeyBindings bindings) = do
  assign _keybindings bindings
  void $ query _marloweEditorPageSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction _ (HandleEditorMessage (Monaco.TextChanged text)) = do
  assign _selectedHole Nothing
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey text
  analysisState <- use _analysisState
  let
    parsedContract = parseContract text

    unreachableContracts = getUnreachableContracts analysisState

    (Tuple markerData additionalContext) = Linter.markers unreachableContracts parsedContract
  markers <- query _marloweEditorPageSlot unit (Monaco.SetModelMarkers markerData identity)
  traverse_ editorSetMarkers markers
  {-
    There are three different Monaco objects that require the linting information:
      * Markers
      * Code completion (type aheads)
      * Code suggestions (Quick fixes)
     To avoid having to recalculate the linting multiple times, we add aditional context to the providers
     whenever the code changes.
  -}
  providers <- query _marloweEditorPageSlot unit (Monaco.GetObjects identity)
  case providers of
    Just { codeActionProvider: Just caProvider, completionItemProvider: Just ciProvider } -> pure $ updateAdditionalContext caProvider ciProvider additionalContext
    _ -> pure unit

handleAction _ (HandleDragEvent event) = liftEffect $ preventDefault event

handleAction settings (HandleDropEvent event) = do
  liftEffect $ preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ editorSetValue contents

handleAction _ (MoveToPosition lineNumber column) = do
  void $ query _marloweEditorPageSlot unit (Monaco.SetPosition { column, lineNumber } unit)

handleAction settings (LoadScript key) = do
  for_ (preview (ix key) StaticData.marloweContracts) \contents -> do
    let
      prettyContents = case parseContract contents of
        Right pcon -> show $ pretty pcon
        Left _ -> contents
    editorSetValue prettyContents
    liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey prettyContents

handleAction settings (SetEditorText contents) = do
  editorSetValue contents

handleAction settings (BottomPanelAction (BottomPanel.PanelAction action)) = handleAction settings action

handleAction _ (BottomPanelAction action) = do
  toBottomPanel (BottomPanel.handleAction action)
  editorResize

handleAction _ (ShowErrorDetail val) = assign _showErrorDetail val

handleAction _ SendToSimulator = pure unit

handleAction _ ViewAsBlockly = pure unit

handleAction _ (InitMarloweProject contents) = do
  editorSetValue contents
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey contents

handleAction _ (SelectHole hole) = assign _selectedHole hole

handleAction settings AnalyseContract = do
  mContents <- editorGetValue
  for_ mContents $ analyseContract settings

handleAction settings AnalyseReachabilityContract = do
  mContents <- editorGetValue
  for_ mContents $ analyseReachability settings

handleAction settings AnalyseContractForCloseRefund =
  void
    $ runMaybeT do
        contents <- MaybeT $ editorGetValue
        contract <- hoistMaybe $ parseContract' contents
        -- when editor and simulator were together the analyse contract could be made
        -- at any step of the simulator. Now that they are separate, it can only be done
        -- with initial state
        let
          emptySemanticState = emptyState zero
        newCloseAnalysisState <- lift $ startCloseAnalysis settings contract emptySemanticState
        assign _analysisState (CloseAnalysis newCloseAnalysisState)

handleAction _ Save = pure unit

parseContract' :: String -> Maybe Contract
parseContract' = fromTerm <=< hush <<< parseContract

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

editorResize :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorResize = void $ query _marloweEditorPageSlot unit (Monaco.Resize unit)

editorSetValue :: forall state action msg m. String -> HalogenM state action ChildSlots msg m Unit
editorSetValue contents = void $ query _marloweEditorPageSlot unit (Monaco.SetText contents unit)

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _marloweEditorPageSlot unit (Monaco.GetText identity)

-- FIXME: This receives markers and sets errors and warnings. Maybe rename to processErrorsAndWarnings
editorSetMarkers :: forall m. MonadEffect m => Array IMarker -> HalogenM State Action ChildSlots Void m Unit
editorSetMarkers markers = do
  let
    errors = filter (\{ severity } -> isError severity) markers

    warnings = filter (\{ severity } -> isWarning severity) markers

    -- The initial message of a hole warning is very lengthy, so we trim it before
    -- displaying it.
    -- see https://github.com/input-output-hk/plutus/pull/2560#discussion_r550252989
    warningsWithTrimmedHoleMessage =
      map
        ( \marker ->
            let
              trimmedMessage =
                if String.take 6 marker.source == "Hole: " then
                  String.takeWhile (\c -> c /= codePointFromChar '\n') marker.message
                else
                  marker.message
            in
              marker { message = trimmedMessage }
        )
        warnings
  modify_
    ( set _editorWarnings warningsWithTrimmedHoleMessage
        <<< set _editorErrors errors
    )
