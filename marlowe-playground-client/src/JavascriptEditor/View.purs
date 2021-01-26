module JavascriptEditor.View where

import Prelude hiding (div)
import BottomPanel.Types (Action(..)) as BottomPanel
import BottomPanel.View (render) as BottomPanel
import Data.Array as Array
import Data.Enum (toEnum, upFromIncluding)
import Data.Lens (to, view, (^.))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML)
import Halogen.Classes (aHorizontal, codeEditor, group)
import Halogen.Classes as Classes
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (HTML, a, button, code_, div, div_, option, pre_, section, select, slot, text)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (class_, classes, enabled, href)
import Halogen.HTML.Properties as HTML
import JavascriptEditor.State (mkEditor)
import JavascriptEditor.Types (Action(..), BottomPanelView(..), State, _bottomPanelState, _compilationResult, _keybindings, isCompiling)
import JavascriptEditor.Types as JS
import Language.Javascript.Interpreter (CompilationError(..), InterpreterResult(..))
import MainFrame.Types (ChildSlots, _jsEditorSlot)
import StaticAnalysis.BottomPanel (analysisResultPane, analyzeButton)
import StaticAnalysis.Types (_analysisState, isCloseAnalysisLoading, isReachabilityLoading, isStaticLoading)
import Text.Pretty (pretty)

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ section [ class_ (ClassName "code-panel") ]
        [ div [ classes [ codeEditor ] ]
            [ jsEditor state ]
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
    ]

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
    (JS.CompiledSuccessfully _) -> true
    _ -> false

editorOptions :: forall p. State -> HTML p Action
editorOptions state =
  div [ class_ (ClassName "editor-options") ]
    [ select
        [ HTML.id_ "editor-options"
        , class_ (ClassName "dropdown-header")
        , HTML.value $ show $ state ^. _keybindings
        , onSelectedIndexChange (\idx -> ChangeKeyBindings <$> toEnum idx)
        ]
        (map keybindingItem (upFromIncluding bottom))
    ]
  where
  keybindingItem item =
    if state ^. _keybindings == item then
      option [ class_ (ClassName "selected-item"), HTML.value (show item) ] [ text $ show item ]
    else
      option [ HTML.value (show item) ] [ text $ show item ]

jsEditor ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
jsEditor state = slot _jsEditorSlot unit mkEditor unit (Just <<< HandleEditorMessage)

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
    JS.Compiling -> "Compiling..."
    (JS.CompiledSuccessfully _) -> "Compiled"
    (JS.CompilationError _) -> "Compiled"
    JS.NotCompiled -> "Compile"

  enabled' = case view _compilationResult state of
    JS.NotCompiled -> true
    _ -> false

  classes' =
    [ ClassName "btn" ]
      <> case view _compilationResult state of
          (JS.CompiledSuccessfully _) -> [ ClassName "success" ]
          (JS.CompilationError _) -> [ ClassName "error" ]
          _ -> []

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state GeneratedOutputView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents ]
    ] case view _compilationResult state of
    JS.CompiledSuccessfully (InterpreterResult result) ->
      [ div [ classes [ ClassName "code-editor", ClassName "expanded", ClassName "code" ] ]
          numberedText
      ]
      where
      numberedText = (code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") ((show <<< pretty <<< _.result) result)
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
    JS.CompilationError err -> [ compilationErrorPane err ]
    _ -> [ text "No errors" ]

compilationErrorPane :: forall p. CompilationError -> HTML p Action
compilationErrorPane (RawError error) = div_ [ text "There was an error when running the JavaScript code:", code_ [ pre_ [ text $ error ] ] ]

compilationErrorPane (JSONParsingError error) = div_ [ text "There was an error when parsing the resulting JSON:", code_ [ pre_ [ text $ error ] ], text "Please, use the JS API provided (see tutorial and examples). If you did use the JS API and still get this error, kindly report the problem at ", a [ href "https://github.com/input-output-hk/plutus/issues/new" ] [ text "https://github.com/input-output-hk/plutus/issues/new" ], text " including the code that caused the error. Thank you" ]

compilationErrorPane (CompilationError error) =
  div
    [ class_ $ ClassName "compilation-error"
    ]
    [ text $ "There is a syntax error in line " <> show error.row <> ", column " <> show error.column <> ":"
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]
