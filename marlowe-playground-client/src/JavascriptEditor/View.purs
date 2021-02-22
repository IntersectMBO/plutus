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
import Halogen.Classes (bgWhite, flex, flexCol, flexGrow, fullHeight, group, maxH70p, minH0, overflowHidden, paddingX, spaceBottom)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (HTML, a, button, code_, div, div_, option, pre_, section, section_, select, slot, text)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (class_, classes, enabled, href)
import Halogen.HTML.Properties as HTML
import JavascriptEditor.State (mkEditor)
import JavascriptEditor.Types (Action(..), BottomPanelView(..), State, _bottomPanelState, _compilationResult, _keybindings)
import JavascriptEditor.Types as JS
import Language.Javascript.Interpreter (CompilationError(..), InterpreterResult(..))
import MainFrame.Types (ChildSlots, _jsEditorSlot)
import StaticAnalysis.BottomPanel (analysisResultPane, analyzeButton, clearButton)
import StaticAnalysis.Types (_analysisExecutionState, _analysisState, isCloseAnalysisLoading, isNoneAsked, isReachabilityLoading, isStaticLoading)
import Text.Pretty (pretty)

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classes [ flex, flexCol, fullHeight ] ]
    [ section [ classes [ paddingX, minH0, flexGrow, overflowHidden ] ]
        [ jsEditor state ]
    , section [ classes [ paddingX, maxH70p ] ]
        [ renderSubmodule
            _bottomPanelState
            BottomPanelAction
            (BottomPanel.render panelTitles wrapBottomPanelContents)
            state
        ]
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
    JS.CompiledSuccessfully _ -> true
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
    JS.CompiledSuccessfully _ -> "Compiled"
    JS.CompilationError _ -> "Compiled"
    JS.NotCompiled -> "Compile"

  enabled' = case view _compilationResult state of
    JS.NotCompiled -> true
    _ -> false

  classes' =
    [ ClassName "btn" ]
      <> case view _compilationResult state of
          JS.CompiledSuccessfully _ -> [ ClassName "success" ]
          JS.CompilationError _ -> [ ClassName "error" ]
          _ -> []

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state GeneratedOutputView =
  section_ case view _compilationResult state of
    JS.CompiledSuccessfully (InterpreterResult result) ->
      [ div [ classes [ bgWhite, spaceBottom, ClassName "code" ] ]
          numberedText
      ]
      where
      numberedText = (code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") ((show <<< pretty <<< _.result) result)
    _ -> [ text "There is no generated code" ]

panelContents state StaticAnalysisView =
  section_
    ( [ analysisResultPane SetIntegerTemplateParam state
      , analyzeButton loadingWarningAnalysis analysisEnabled "Analyse for warnings" AnalyseContract
      , analyzeButton loadingReachability analysisEnabled "Analyse reachability" AnalyseReachabilityContract
      , analyzeButton loadingCloseAnalysis analysisEnabled "Analyse for refunds on Close" AnalyseContractForCloseRefund
      , clearButton clearEnabled "Clear" ClearAnalysisResults
      ]
        <> (if isCompiled then [] else [ div [ classes [ ClassName "choice-error" ] ] [ text "JavaScript code needs to be compiled in order to run static analysis" ] ])
    )
  where
  loadingWarningAnalysis = state ^. _analysisState <<< _analysisExecutionState <<< to isStaticLoading

  loadingReachability = state ^. _analysisState <<< _analysisExecutionState <<< to isReachabilityLoading

  loadingCloseAnalysis = state ^. _analysisState <<< _analysisExecutionState <<< to isCloseAnalysisLoading

  noneAskedAnalysis = state ^. _analysisState <<< _analysisExecutionState <<< to isNoneAsked

  anyAnalysisLoading = loadingWarningAnalysis || loadingReachability || loadingCloseAnalysis

  analysisEnabled = not anyAnalysisLoading && isCompiled

  clearEnabled = not (anyAnalysisLoading || noneAskedAnalysis)

  isCompiled = case view _compilationResult state of
    JS.CompiledSuccessfully _ -> true
    _ -> false

panelContents state ErrorsView =
  section_ case view _compilationResult state of
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
