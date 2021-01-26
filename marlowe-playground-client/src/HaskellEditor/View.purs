module HaskellEditor.View where

import Prelude hiding (div)
import BottomPanel.Types (Action(..)) as BottomPanel
import BottomPanel.View (render) as BottomPanel
import Data.Array as Array
import Data.Either (Either(..))
import Data.Enum (toEnum, upFromIncluding)
import Data.Lens (to, view, (^.))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML)
import Halogen.Classes (aHorizontal, codeEditor, group, spaceBottom, spaceRight, spaceTop)
import Halogen.Classes as Classes
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (HTML, button, code_, div, div_, option, pre_, section, select, slot, text)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (class_, classes, enabled)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (monacoComponent)
import HaskellEditor.Types (Action(..), BottomPanelView(..), State, _bottomPanelState, _compilationResult, _haskellEditorKeybindings, isCompiling)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult(..))
import Language.Haskell.Monaco as HM
import MainFrame.Types (ChildSlots, _haskellEditorSlot)
import Network.RemoteData (RemoteData(..))
import StaticAnalysis.BottomPanel (analysisResultPane)
import StaticAnalysis.Types (_analysisState, isCloseAnalysisLoading, isReachabilityLoading, isStaticLoading)

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ section [ class_ (ClassName "code-panel") ]
        [ div [ classes [ codeEditor ] ]
            [ haskellEditor state ]
        ]
    , renderSubmodule _bottomPanelState BottomPanelAction (BottomPanel.render panelTitles wrapBottomPanelContents) state
    ]
  where
  panelTitles =
    [ { title: "Generated code", view: GeneratedOutputView, classes: [] }
    , { title: "Static Analysis", view: StaticAnalysisView, classes: [] }
    , { title: "Errors", view: ErrorsView, classes: [] }
    ]

  wrapBottomPanelContents panelView = BottomPanel.PanelAction <$> panelContents state panelView

otherActions :: forall p. State -> HTML p Action
otherActions state =
  div [ classes [ group ] ]
    [ editorOptions state
    , compileButton state
    , sendToSimulationButton state
    -- FIXME: I think we want to change this action to be called from the simulator
    --        with the action "soon to be implemented" ViewAsBlockly
    -- , sendResultButton state "Send To Blockly" SendResultToBlockly
    ]

editorOptions :: forall p. State -> HTML p Action
editorOptions state =
  div [ class_ (ClassName "editor-options") ]
    [ select
        [ HTML.id_ "editor-options"
        , class_ (ClassName "dropdown-header")
        , HTML.value $ show $ state ^. _haskellEditorKeybindings
        , onSelectedIndexChange (\idx -> ChangeKeyBindings <$> toEnum idx)
        ]
        (map keybindingItem (upFromIncluding bottom))
    ]
  where
  keybindingItem item =
    if state ^. _haskellEditorKeybindings == item then
      option [ class_ (ClassName "selected-item"), HTML.value (show item) ] [ text $ show item ]
    else
      option [ HTML.value (show item) ] [ text $ show item ]

haskellEditor ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
haskellEditor state = slot _haskellEditorSlot unit component unit (Just <<< HandleEditorMessage)
  where
  setup editor = pure unit

  component = monacoComponent $ HM.settings setup

compileButton :: forall p. State -> HTML p Action
compileButton state =
  button
    [ onClick $ const $ Just Compile
    , enabled enabled'
    , classes classes'
    ]
    [ text buttonText ]
  where
  buttonText = case view _compilationResult state of
    Loading -> "Compiling..."
    (Success _) -> "Compiled"
    _ -> "Compile"

  enabled' = case view _compilationResult state of
    NotAsked -> true
    _ -> false

  classes' =
    [ ClassName "btn" ]
      <> case view _compilationResult state of
          (Success (Right _)) -> [ ClassName "success" ]
          (Success (Left _)) -> [ ClassName "error" ]
          _ -> []

sendToSimulationButton :: forall p. State -> HTML p Action
sendToSimulationButton state =
  button
    [ onClick $ const $ Just SendResultToSimulator
    , enabled enabled'
    ]
    [ text "Send To Simulator" ]
  where
  compilationResult = view _compilationResult state

  enabled' = case compilationResult of
    Success (Right (InterpreterResult _)) -> true
    _ -> false

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state GeneratedOutputView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents ]
    ] case view _compilationResult state of
    Success (Right (InterpreterResult result)) ->
      [ div [ classes [ ClassName "code-editor", ClassName "expanded", ClassName "code" ] ]
          numberedText
      ]
      where
      numberedText = (code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") result.result
    _ -> [ text "There is no generated code" ]

panelContents state StaticAnalysisView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents ]
    ]
    [ analysisResultPane state
    , analyzeButton loadingAnalyseContract enabled' "Analyse for warnings" AnalyseContract
    , analyzeButton loadingReachability enabled' "Analyse reachability" AnalyseReachabilityContract
    , analyzeButton loadingCloseAnalysis enabled' "Analyse for refunds on Close" AnalyseContractForCloseRefund
    ]
  where
  loadingAnalyseContract = state ^. _analysisState <<< to isStaticLoading

  -- FIXME: I need to make this work for loading and not started
  loadingReachability = state ^. _analysisState <<< to isReachabilityLoading

  loadingCloseAnalysis = state ^. _analysisState <<< to isCloseAnalysisLoading

  enabled' = not loadingAnalyseContract && not (isCompiling state)

panelContents state ErrorsView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents ]
    ] case view _compilationResult state of
    Success (Left (TimeoutError error)) -> [ text error ]
    Success (Left (CompilationErrors errors)) -> map compilationErrorPane errors
    _ -> [ text "No errors" ]

analyzeButton ::
  forall p. Boolean -> Boolean -> String -> Action -> HTML p Action
analyzeButton isLoading isEnabled name action =
  button
    [ onClick $ const $ Just $ action
    , enabled isEnabled
    , classes [ spaceTop, spaceBottom, spaceRight ]
    ]
    [ text (if isLoading then "Analysing..." else name) ]

compilationErrorPane :: forall p. CompilationError -> HTML p Action
compilationErrorPane (RawError error) = div_ [ text error ]

compilationErrorPane (CompilationError error) =
  div
    [ class_ $ ClassName "compilation-error"
    ]
    [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":"
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]
