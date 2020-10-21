module HaskellEditor where

import Prelude hiding (div)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Array (catMaybes)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Enum (toEnum, upFromIncluding)
import Data.Lens (assign, to, use, view, (^.))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Examples.Haskell.Contracts as HE
import Halogen (ClassName(..), ComponentHTML, HalogenM, liftEffect, query)
import Halogen.Blockly as Blockly
import Halogen.Classes (aHorizontal, activeClasses, analysisPanel, closeDrawerArrowIcon, codeEditor, collapsed, footerPanelBg, jFlexStart, minimizeIcon, panelSubHeader, panelSubHeaderMain, spaceLeft)
import Halogen.HTML (HTML, a, button, code_, div, div_, img, li, option, pre_, section, select, slot, small_, text, ul)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (alt, class_, classes, disabled, src)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import Halogen.Monaco (monacoComponent)
import HaskellEditor.Types (Action(..), State, _activeHaskellDemo, _compilationResult, _haskellEditorKeybindings, _showBottomPanel)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult(..), _InterpreterResult)
import Language.Haskell.Monaco as HM
import LocalStorage as LocalStorage
import Marlowe (SPParams_, postRunghc)
import Monaco (IMarkerData, markerSeverity)
import Monaco (getModel, setValue) as Monaco
import Network.RemoteData (RemoteData(..), isLoading, isSuccess)
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import Simulation.State (_result)
import Simulation.Types (WebData)
import StaticData (bufferLocalStorageKey)
import StaticData as StaticData
import Types (ChildSlots, _blocklySlot, _haskellEditorSlot, bottomPanelHeight)
import Webghc.Server (CompileRequest(..))

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction _ (HandleEditorMessage (Monaco.TextChanged text)) = do
  liftEffect $ LocalStorage.setItem bufferLocalStorageKey text
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
  pure unit

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

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ section [ classes [ panelSubHeader, aHorizontal ] ]
        [ div [ classes [ panelSubHeaderMain, aHorizontal ] ]
            [ div [ classes [ ClassName "demo-title", aHorizontal, jFlexStart ] ]
                [ div [ classes [ ClassName "demos", spaceLeft ] ]
                    [ small_ [ text "Demos:" ]
                    ]
                ]
            , ul [ classes [ ClassName "demo-list", aHorizontal ] ]
                (demoScriptLink <$> Array.fromFoldable (Map.keys StaticData.demoFiles))
            ]
        , div [ class_ (ClassName "editor-options") ]
            [ select
                [ HTML.id_ "editor-options"
                , class_ (ClassName "dropdown-header")
                , onSelectedIndexChange (\idx -> ChangeKeyBindings <$> toEnum idx)
                ]
                (map keybindingItem (upFromIncluding bottom))
            ]
        ]
    , section [ class_ (ClassName "code-panel") ]
        [ div [ classes (codeEditor $ state ^. _showBottomPanel) ]
            [ haskellEditor state ]
        ]
    ]
  where
  keybindingItem item =
    if state ^. _haskellEditorKeybindings == item then
      option [ class_ (ClassName "selected-item"), HTML.value (show item) ] [ text $ show item ]
    else
      option [ HTML.value (show item) ] [ text $ show item ]

  demoScriptLink key = li [ state ^. _activeHaskellDemo <<< activeClasses (eq key) ] [ a [ onClick $ const $ Just $ LoadScript key ] [ text key ] ]

haskellEditor ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
haskellEditor state = slot _haskellEditorSlot unit component unit (Just <<< HandleEditorMessage)
  where
  setup editor =
    liftEffect do
      mContents <- LocalStorage.getItem StaticData.bufferLocalStorageKey
      let
        contents = fromMaybe HE.escrow mContents
      model <- Monaco.getModel editor
      Monaco.setValue model contents

  component = monacoComponent $ HM.settings setup

bottomPanel :: forall p. State -> HTML p Action
bottomPanel state =
  div
    ( [ classes
          ( if showingBottomPanel then
              [ analysisPanel ]
            else
              [ analysisPanel, collapsed ]
          )
      , bottomPanelHeight showingBottomPanel
      ]
    )
    [ div
        [ classes [ footerPanelBg, ClassName "flip-x" ] ]
        [ section [ classes [ ClassName "panel-header", aHorizontal ] ]
            [ div [ classes [ ClassName "panel-sub-header-main", aHorizontal ] ]
                [ div [ class_ (ClassName "minimize-icon-container") ]
                    [ a [ onClick $ const $ Just $ ShowBottomPanel (state ^. _showBottomPanel <<< to not) ]
                        [ img [ classes (minimizeIcon $ state ^. _showBottomPanel), src closeDrawerArrowIcon, alt "close drawer icon" ] ]
                    ]
                , div
                    [ classes ([ ClassName "panel-tab", aHorizontal, ClassName "haskell-buttons" ])
                    ]
                    [ button [ onClick $ const $ Just Compile ] [ text (if state ^. _compilationResult <<< to isLoading then "Compiling..." else "Compile") ]
                    , sendResultButton state "Send To Simulator" SendResultToSimulator
                    , sendResultButton state "Send To Blockly" SendResultToBlockly
                    ]
                ]
            ]
        , section
            [ classes [ ClassName "panel-sub-header", aHorizontal, ClassName "panel-contents" ]
            ]
            (resultPane state)
        ]
    ]
  where
  showingBottomPanel = state ^. _showBottomPanel

sendResultButton :: forall p. State -> String -> Action -> HTML p Action
sendResultButton state msg action =
  let
    compilationResult = view _compilationResult state
  in
    case view _compilationResult state of
      Success (Right (InterpreterResult result)) ->
        button
          [ onClick $ const $ Just action
          , disabled (isLoading compilationResult || (not isSuccess) compilationResult)
          ]
          [ text msg ]
      _ -> text ""

resultPane :: forall p. State -> Array (HTML p Action)
resultPane state =
  if state ^. _showBottomPanel then case view _compilationResult state of
    Success (Right (InterpreterResult result)) ->
      [ div [ classes [ ClassName "code-editor", ClassName "expanded", ClassName "code" ] ]
          numberedText
      ]
      -- [ code_
      --     [ pre [ class_ $ ClassName "success-code" ] [ text (unwrap result.result) ]
      --     ]
      -- ]
      where
      numberedText = (code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") result.result
    Success (Left (TimeoutError error)) -> [ text error ]
    Success (Left (CompilationErrors errors)) -> map compilationErrorPane errors
    _ -> [ text "" ]
  else
    [ text "" ]

compilationErrorPane :: forall p. CompilationError -> HTML p Action
compilationErrorPane (RawError error) = div_ [ text error ]

compilationErrorPane (CompilationError error) =
  div
    [ class_ $ ClassName "compilation-error"
    ]
    [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":"
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]
