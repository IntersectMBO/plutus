module MarloweEditor.State
  ( handleAction
  , editorGetValue
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
import Data.Array as Array
import Data.Either (Either(..), hush)
import Data.Foldable (for_)
import Data.Lens (assign, modifying, over, preview, set, use)
import Data.Lens.Index (ix)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String (Pattern(..), codePointFromChar, contains)
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff, liftAff)
import Env (Env)
import Examples.Marlowe.Contracts (example) as ME
import Halogen (HalogenM, liftEffect, modify_, query)
import Halogen as H
import Halogen.Extra (mapSubmodule)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import MainFrame.Types (ChildSlots, _marloweEditorPageSlot)
import Marlowe.Extended (TemplateContent)
import Marlowe.Extended as Extended
import Marlowe.Extended.Metadata (MetadataHintInfo)
import Marlowe.Holes as Holes
import Marlowe.LinterText as Linter
import Marlowe.Monaco (updateAdditionalContext)
import Marlowe.Monaco as MM
import Marlowe.Parser (parseContract)
import MarloweEditor.Types (Action(..), BottomPanelView, State, _hasHoles, _bottomPanelState, _editorErrors, _editorWarnings, _keybindings, _metadataHintInfo, _selectedHole, _showErrorDetail)
import Monaco (isError, isWarning)
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import SessionStorage as SessionStorage
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
  mContents <- liftEffect $ SessionStorage.getItem marloweBufferLocalStorageKey
  editorSetValue $ fromMaybe ME.example mContents

handleAction (ChangeKeyBindings bindings) = do
  assign _keybindings bindings
  void $ query _marloweEditorPageSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction (HandleEditorMessage (Monaco.TextChanged text)) = do
  assign _selectedHole Nothing
  liftEffect $ SessionStorage.setItem marloweBufferLocalStorageKey text
  processMarloweCode text

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
    liftEffect $ SessionStorage.setItem marloweBufferLocalStorageKey prettyContents

handleAction (SetEditorText contents) = editorSetValue contents

handleAction (BottomPanelAction (BottomPanel.PanelAction action)) = handleAction action

handleAction (BottomPanelAction action) = do
  toBottomPanel (BottomPanel.handleAction action)

handleAction (ShowErrorDetail val) = assign _showErrorDetail val

handleAction SendToSimulator = pure unit

handleAction ViewAsBlockly = pure unit

handleAction (InitMarloweProject contents) = do
  editorSetValue contents
  liftEffect $ SessionStorage.setItem marloweBufferLocalStorageKey contents

handleAction (SelectHole hole) = assign _selectedHole hole

handleAction (SetIntegerTemplateParam templateType key value) = modifying (_analysisState <<< _templateContent <<< Extended.typeToLens templateType) (Map.insert key value)

handleAction (MetadataAction _) = pure unit

handleAction AnalyseContract = runAnalysis $ analyseContract

handleAction AnalyseReachabilityContract = runAnalysis $ analyseReachability

handleAction AnalyseContractForCloseRefund = runAnalysis $ analyseClose

handleAction ClearAnalysisResults = do
  assign (_analysisState <<< _analysisExecutionState) NoneAsked
  mContents <- editorGetValue
  for_ mContents \contents -> processMarloweCode contents

handleAction Save = pure unit

runAnalysis ::
  forall m.
  MonadAff m =>
  (Extended.Contract -> HalogenM State Action ChildSlots Void m Unit) ->
  HalogenM State Action ChildSlots Void m Unit
runAnalysis doAnalyze =
  void
    $ runMaybeT do
        contents <- MaybeT $ editorGetValue
        contract <- hoistMaybe $ parseContract' contents
        lift
          $ do
              doAnalyze contract
              processMarloweCode contents

parseContract' :: String -> Maybe Extended.Contract
parseContract' = Holes.fromTerm <=< hush <<< parseContract

-- This function makes all the heavy processing needed to have the Editor state in sync with current changes.
processMarloweCode ::
  forall m.
  MonadAff m =>
  String ->
  HalogenM State Action ChildSlots Void m Unit
processMarloweCode text = do
  analysisExecutionState <- use (_analysisState <<< _analysisExecutionState)
  oldMetadataInfo <- use _metadataHintInfo
  let
    eParsedContract = parseContract text

    unreachableContracts = getUnreachableContracts analysisExecutionState

    (Tuple markerData additionalContext) = Linter.markers unreachableContracts eParsedContract

    errorMarkers =
      markerData
        # Array.filter (isError <<< _.severity)

    -- The initial message of a hole warning is very lengthy, so we trim it before
    -- displaying it.
    -- see https://github.com/input-output-hk/plutus/pull/2560#discussion_r550252989
    warningMarkers =
      markerData
        # Array.filter (isWarning <<< _.severity)
        <#> \marker ->
            let
              trimmedMessage =
                if String.take 6 marker.source == "Hole: " then
                  String.takeWhile (\c -> c /= codePointFromChar '\n') marker.message
                else
                  marker.message
            in
              marker { message = trimmedMessage }

    mContract :: Maybe Extended.Contract
    mContract = Holes.fromTerm =<< hush eParsedContract

    metadataInfo :: MetadataHintInfo
    metadataInfo = fromMaybe oldMetadataInfo additionalContext.metadataHints

    hasHoles =
      not $ Array.null
        $ Array.filter (contains (Pattern "hole") <<< _.message) warningMarkers

    -- If we can get an Extended contract from the holes contract (basically if it has no holes)
    -- then update the template content. If not, leave them as they are
    maybeUpdateTemplateContent :: TemplateContent -> TemplateContent
    maybeUpdateTemplateContent = maybe identity (Extended.updateTemplateContent <<< Extended.getPlaceholderIds) mContract
  void $ query _marloweEditorPageSlot unit $ H.request $ Monaco.SetModelMarkers markerData
  modify_
    ( set _editorWarnings warningMarkers
        <<< set _editorErrors errorMarkers
        <<< set _hasHoles hasHoles
        <<< over (_analysisState <<< _templateContent) maybeUpdateTemplateContent
        <<< set _metadataHintInfo metadataInfo
    )
  {-
    There are three different Monaco objects that require the linting information:
      * Markers
      * Code completion (type aheads)
      * Code suggestions (Quick fixes)
     To avoid having to recalculate the linting multiple times, we add aditional context to the providers
     whenever the code changes.
  -}
  mProviders <- query _marloweEditorPageSlot unit (Monaco.GetObjects identity)
  case mProviders of
    Just { codeActionProvider: Just caProvider, completionItemProvider: Just ciProvider } -> pure $ updateAdditionalContext caProvider ciProvider additionalContext
    _ -> pure unit

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

editorSetTheme :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorSetTheme = void $ query _marloweEditorPageSlot unit (Monaco.SetTheme MM.daylightTheme.name unit)

editorSetValue :: forall state action msg m. String -> HalogenM state action ChildSlots msg m Unit
editorSetValue contents = void $ query _marloweEditorPageSlot unit (Monaco.SetText contents unit)

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _marloweEditorPageSlot unit (Monaco.GetText identity)
