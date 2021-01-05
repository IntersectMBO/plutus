module MarloweEditor.State
  ( handleAction
  , editorGetValue
  , {- FIXME: this should be an action -} editorResize
  ) where

import Prelude hiding (div)
import Control.Monad.Except (ExceptT, lift, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader (runReaderT)
import Data.Array (filter)
import Data.Either (Either(..), hush)
import Data.Foldable (for_)
import Data.Lens (assign, preview, set, use)
import Data.Lens.Index (ix)
import Data.Maybe (Maybe(..))
import Data.String (codePointFromChar)
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import FileEvents (readFileFromDragEvent)
import FileEvents as FileEvents
import Halogen (HalogenM, liftEffect, modify_, query)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _hasUnsavedChanges', _marloweEditorPageSlot)
import Marlowe (SPParams_)
import Marlowe as Server
import Marlowe.Holes (fromTerm)
import Marlowe.Linter as Linter
import Marlowe.Monaco (updateAdditionalContext)
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (Contract, emptyState)
import Marlowe.Symbolic.Types.Request as MSReq
import MarloweEditor.Types (Action(..), AnalysisState(..), State, _analysisState, _bottomPanelView, _editorErrors, _editorWarnings, _keybindings, _selectedHole, _showBottomPanel)
import Monaco (IMarker, isError, isWarning)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import StaticAnalysis.Reachability (getUnreachableContracts, startReachabilityAnalysis)
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (marloweBufferLocalStorageKey)
import StaticData as StaticData
import Text.Pretty (pretty)
import Types (WebData)

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
  modify_
    ( set _selectedHole Nothing
        <<< set _hasUnsavedChanges' true
    )
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey text
  analysisState <- use _analysisState
  let
    parsedContract = parseContract text

    unreachableContracts = getUnreachableContracts analysisState

    (Tuple markerData additionalContext) = Linter.markers unreachableContracts parsedContract
  markers <- query _marloweEditorPageSlot unit (Monaco.SetModelMarkers markerData identity)
  void $ traverse editorSetMarkers markers
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

handleAction _ (HandleDragEvent event) = liftEffect $ FileEvents.preventDefault event

handleAction settings (HandleDropEvent event) = do
  liftEffect $ FileEvents.preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ editorSetValue contents
  -- updateContractInState contents --FIXME
  -- FIXME: check but I don't think this is needed after the split
  -- setOraclePrice settings
  -- pure unit is only here so the comment stays in place
  pure unit

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
    --FIXME
    -- updateContractInState prettyContents
    -- resetContract
    -- setOraclePrice settings
    -- pure unit is only here so the comment stays in place
    pure unit

handleAction settings (SetEditorText contents) = do
  editorSetValue contents
  -- FIXME
  -- updateContractInState contents
  -- pure unit is only here so the comment stays in place
  pure unit

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  editorResize

handleAction _ (ShowErrorDetail val) =  {- FIXME assign _showErrorDetail val -} pure unit

handleAction _ (ChangeBottomPanelView view) = do
  assign _bottomPanelView view
  assign _showBottomPanel true
  editorResize

handleAction _ SendToSimulator = pure unit

handleAction _ ViewAsBlockly = pure unit

handleAction _ (InitMarloweProject contents) = do
  editorSetValue contents
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey contents
  assign _hasUnsavedChanges' false

handleAction _ MarkProjectAsSaved = assign _hasUnsavedChanges' false

handleAction settings AnalyseContract =
  void
    $ runMaybeT do
        contents <- MaybeT $ editorGetValue
        contract <- hoistMaybe $ parseContract' contents
        -- FIXME: when editor and simulator were together the analyse contract could be made
        --        at any step of the simulator. Now that they are separate, it can only be done
        --        with initial state
        let
          emptySemanticState = emptyState zero
        assign _analysisState (WarningAnalysis Loading)
        response <- lift $ checkContractForWarnings contract emptySemanticState
        assign _analysisState (WarningAnalysis response)
  where
  checkContractForWarnings contract state = runAjax $ (flip runReaderT) settings (Server.postMarloweanalysis (MSReq.Request { onlyAssertions: false, contract, state }))

handleAction settings AnalyseReachabilityContract =
  void
    $ runMaybeT do
        contents <- MaybeT $ editorGetValue
        contract <- hoistMaybe $ parseContract' contents
        -- FIXME: when editor and simulator were together the analyse contract could be made
        --        at any step of the simulator. Now that they are separate, it can only be done
        --        with initial state
        let
          emptySemanticState = emptyState zero
        newReachabilityAnalysisState <- lift $ startReachabilityAnalysis settings contract emptySemanticState
        assign _analysisState (ReachabilityAnalysis newReachabilityAnalysisState)

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
    warnings = filter (\{ severity } -> isWarning severity) markers

    trimHoles =
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
  let
    errors = filter (\{ severity } -> isError severity) markers
  modify_
    ( set _editorWarnings trimHoles
        <<< set _editorErrors errors
    )
