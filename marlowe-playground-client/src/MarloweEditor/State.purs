module MarloweEditor.State
  ( handleAction
  , editorGetValue
  , {- FIXME: this should be an action -} editorResize
  , editorSetTheme
  ) where

import Prelude hiding (div)
import BottomPanel.State (handleAction) as BottomPanel
import BottomPanel.Types (Action(..), State) as BottomPanel
import CloseAnalysis (analyseClose)
import Control.Monad.Except (ExceptT, lift, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader (class MonadAsk)
import Data.Array (filter)
import Data.Either (Either(..), hush)
import Data.Foldable (for_, traverse_)
import Data.Lens (assign, modifying, preview, set, use)
import Data.Lens.Index (ix)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (codePointFromChar)
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Env (Env)
import Examples.Marlowe.Contracts (example) as ME
import Halogen (HalogenM, liftEffect, modify_, query)
import Halogen.Extra (mapSubmodule)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _marloweEditorPageSlot)
import Marlowe.Extended (Contract, getPlaceholderIds, typeToLens, updateTemplateContent)
import Marlowe.Holes (fromTerm)
import Marlowe.LinterText as Linter
import Marlowe.Monaco (updateAdditionalContext)
import Marlowe.Monaco as MM
import Marlowe.Parser (parseContract)
import MarloweEditor.Types (Action(..), BottomPanelView, State, _bottomPanelState, _editorErrors, _editorWarnings, _keybindings, _selectedHole, _showErrorDetail)
import Monaco (IMarker, isError, isWarning)
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import StaticAnalysis.Reachability (analyseReachability, getUnreachableContracts)
import StaticAnalysis.StaticTools (analyseContract)
import StaticAnalysis.Types (AnalysisExecutionState(..), _analysisExecutionState, _analysisState, _templateContent)
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
  MonadAsk Env m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction Init = do
  editorSetTheme
  mContents <- liftEffect $ LocalStorage.getItem marloweBufferLocalStorageKey
  editorSetValue $ fromMaybe ME.example mContents

handleAction (ChangeKeyBindings bindings) = do
  assign _keybindings bindings
  void $ query _marloweEditorPageSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction (HandleEditorMessage (Monaco.TextChanged text)) = do
  assign _selectedHole Nothing
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey text
  lintText text

handleAction (HandleDragEvent event) = liftEffect $ preventDefault event

handleAction (HandleDropEvent event) = do
  liftEffect $ preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ editorSetValue contents

handleAction (MoveToPosition lineNumber column) = do
  void $ query _marloweEditorPageSlot unit (Monaco.SetPosition { column, lineNumber } unit)

handleAction (LoadScript key) = do
  for_ (preview (ix key) StaticData.marloweContracts) \contents -> do
    let
      prettyContents = case parseContract contents of
        Right pcon -> show $ pretty pcon
        Left _ -> contents
    editorSetValue prettyContents
    liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey prettyContents

handleAction (SetEditorText contents) = editorSetValue contents

handleAction (BottomPanelAction (BottomPanel.PanelAction action)) = handleAction action

handleAction (BottomPanelAction action) = do
  toBottomPanel (BottomPanel.handleAction action)
  editorResize

handleAction (ShowErrorDetail val) = assign _showErrorDetail val

handleAction SendToSimulator = pure unit

handleAction ViewAsBlockly = pure unit

handleAction (InitMarloweProject contents) = do
  editorSetValue contents
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey contents

handleAction (SelectHole hole) = assign _selectedHole hole

handleAction (SetIntegerTemplateParam templateType key value) = modifying (_analysisState <<< _templateContent <<< typeToLens templateType) (Map.insert key value)

handleAction AnalyseContract = runAnalysis $ analyseContract

handleAction AnalyseReachabilityContract = runAnalysis $ analyseReachability

handleAction AnalyseContractForCloseRefund = runAnalysis $ analyseClose

handleAction ClearAnalysisResults = assign (_analysisState <<< _analysisExecutionState) NoneAsked

handleAction Save = pure unit

runAnalysis ::
  forall m.
  MonadAff m =>
  (Contract -> HalogenM State Action ChildSlots Void m Unit) ->
  HalogenM State Action ChildSlots Void m Unit
runAnalysis doAnalyze =
  void
    $ runMaybeT do
        contents <- MaybeT $ editorGetValue
        contract <- hoistMaybe $ parseContract' contents
        lift
          $ do
              doAnalyze contract
              lintText contents

parseContract' :: String -> Maybe Contract
parseContract' = fromTerm <=< hush <<< parseContract

lintText ::
  forall m.
  MonadAff m =>
  String ->
  HalogenM State Action ChildSlots Void m Unit
lintText text = do
  analysisExecutionState <- use (_analysisState <<< _analysisExecutionState)
  let
    parsedContract = parseContract text

    unreachableContracts = getUnreachableContracts analysisExecutionState

    (Tuple markerData additionalContext) = Linter.markers unreachableContracts parsedContract
  markers <- query _marloweEditorPageSlot unit (Monaco.SetModelMarkers markerData identity)
  traverse_ editorSetMarkers markers
  for_ parsedContract
    ( \contractHoles ->
        for_ ((fromTerm contractHoles) :: Maybe Contract)
          ( \contract ->
              modifying (_analysisState <<< _templateContent) $ updateTemplateContent $ getPlaceholderIds contract
          )
    ) -- We set the templates here so that we don't have to parse twice
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

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

editorSetTheme :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorSetTheme = void $ query _marloweEditorPageSlot unit (Monaco.SetTheme MM.daylightTheme.name unit)

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
