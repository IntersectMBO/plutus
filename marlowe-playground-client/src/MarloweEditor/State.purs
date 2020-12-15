module MarloweEditor.State
  ( handleAction
  , editorGetValue
  , {- FIXME: this should be an action -} editorResize
  ) where

import Prelude hiding (div)
import Data.Array (filter)
import Data.Lens (assign, set, use)
import Data.Maybe (Maybe(..))
import Data.String (codePointFromChar)
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Halogen (HalogenM, liftEffect, modify_, query)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _hasUnsavedChanges', _marloweEditorPageSlot)
import Marlowe (SPParams_)
import Marlowe.Linter as Linter
import Marlowe.Monaco (updateAdditionalContext)
import Marlowe.Parser (parseContract)
import MarloweEditor.Types (Action(..), State, _analysisState, _keybindings, _selectedHole, _showBottomPanel)
import Monaco (IMarker, isError, isWarning)
import Reachability (getUnreachableContracts)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (marloweBufferLocalStorageKey)

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
  -- QUESTION: Why do we need to update providers on every text change?
  providers <- query _marloweEditorPageSlot unit (Monaco.GetObjects identity)
  case providers of
    Just { codeActionProvider: Just caProvider, completionItemProvider: Just ciProvider } -> pure $ updateAdditionalContext caProvider ciProvider additionalContext
    _ -> pure unit

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  editorResize

-- FIXME fix in the Mainframe (refactor from Simulation)
handleAction _ SetBlocklyCode = pure unit

handleAction _ (InitMarloweProject contents) = do
  editorSetValue contents
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey contents
  assign _hasUnsavedChanges' false

handleAction _ MarkProjectAsSaved = assign _hasUnsavedChanges' false

editorResize :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorResize = void $ query _marloweEditorPageSlot unit (Monaco.Resize unit)

editorSetValue :: forall state action msg m. String -> HalogenM state action ChildSlots msg m Unit
editorSetValue contents = void $ query _marloweEditorPageSlot unit (Monaco.SetText contents unit)

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _marloweEditorPageSlot unit (Monaco.GetText identity)

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
  -- FIXME: This is not doing anything at the moment. We were probably hijacking the
  -- errors and warnings from the simulation. We proably need to add editorWarnings and errors
  -- to the MarloweEditor state. Do it later
  -- assign (_marloweState <<< _Head <<< _editorWarnings) trimHoles
  -- assign (_marloweState <<< _Head <<< _editorErrors) errors
  pure unit
