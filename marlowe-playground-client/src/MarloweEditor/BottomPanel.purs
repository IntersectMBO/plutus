module MarloweEditor.BottomPanel
  ( panelContents
  ) where

import Prelude hiding (div)

import Data.Array (drop, head)
import Data.Array as Array
import Data.Lens (to, (^.))
import Data.Maybe (Maybe(..))
import Data.String (take)
import Data.String.Extra (unlines)
import Data.Tuple.Nested ((/\))
import Halogen.Classes (flex, flexCol, fontBold, fullWidth, grid, gridColsDescriptionLocation, justifySelfEnd, minW0, overflowXScroll, paddingRight, underline)
import Halogen.HTML (HTML, a, div, div_, pre_, section, section_, span_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import MarloweEditor.Types (Action(..), BottomPanelView(..), State, _editorErrors, _editorWarnings, _hasHoles, _showErrorDetail, contractHasErrors)
import StaticAnalysis.BottomPanel (analysisResultPane, analyzeButton, clearButton)
import StaticAnalysis.Types (_analysisExecutionState, _analysisState, isCloseAnalysisLoading, isNoneAsked, isReachabilityLoading, isStaticLoading)
import Text.Parsing.StringParser.Basic (lines)

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state StaticAnalysisView =
  section [ classes [ flex, flexCol ] ]
    if (state ^. _hasHoles ) then
      [ div_ [ text "The contract needs to be complete (no holes) before doing static analysis." ]
      ]
    else
      [ analysisResultPane SetIntegerTemplateParam state
      , div [ classes [ paddingRight ] ]
          [ analyzeButton loadingWarningAnalysis analysisEnabled "Analyse for warnings" AnalyseContract
          , analyzeButton loadingReachability analysisEnabled "Analyse reachability" AnalyseReachabilityContract
          , analyzeButton loadingCloseAnalysis analysisEnabled "Analyse for refunds on Close" AnalyseContractForCloseRefund
          , clearButton clearEnabled "Clear" ClearAnalysisResults
          ]
      ]
  where
  loadingWarningAnalysis = state ^. _analysisState <<< _analysisExecutionState <<< to isStaticLoading

  loadingReachability = state ^. _analysisState <<< _analysisExecutionState <<< to isReachabilityLoading

  loadingCloseAnalysis = state ^. _analysisState <<< _analysisExecutionState <<< to isCloseAnalysisLoading

  noneAskedAnalysis = state ^. _analysisState <<< _analysisExecutionState <<< to isNoneAsked

  nothingLoading = not loadingWarningAnalysis && not loadingReachability && not loadingCloseAnalysis

  clearEnabled = nothingLoading && not noneAskedAnalysis

  analysisEnabled = nothingLoading && not contractHasErrors state

panelContents state MarloweWarningsView =
  section_
    if Array.null warnings then
      [ pre_ [ text "No warnings" ] ]
    else
      [ div [ classes [ grid, gridColsDescriptionLocation, fullWidth ] ]
          (headers <> (renderWarning =<< warnings))
      ]
  where
  warnings = state ^. _editorWarnings

  headers =
    [ div [ class_ fontBold ] [ text "Description" ]
    , div [ class_ fontBold ] [ text "Line Number" ]
    ]

  renderWarning warning =
    [ span_ $ [ text warning.message ]
    , a
        [ onClick $ const $ Just $ MoveToPosition warning.startLineNumber warning.startColumn
        , classes [ underline, justifySelfEnd ]
        ]
        [ text $ show warning.startLineNumber ]
    ]

panelContents state MarloweErrorsView =
  section_
    if Array.null errors then
      [ pre_ [ text "No errors" ] ]
    else
      [ div [ classes [ grid, gridColsDescriptionLocation, fullWidth ] ]
          (headers <> (renderError =<< errors))
      ]
  where
  errors = state ^. (_editorErrors <<< to (map formatError))

  headers =
    [ div [ class_ fontBold ] [ text "Description" ]
    , div [ class_ fontBold ] [ text "Line Number" ]
    ]

  renderError error =
    [ div [ classes [ minW0, overflowXScroll ] ]
        ( [ a
              [ onClick $ const $ Just $ ShowErrorDetail (state ^. (_showErrorDetail <<< to not)) ]
              [ text $ (if state ^. _showErrorDetail then "- " else "+ ") <> error.firstLine ]
          ]
            <> if (state ^. _showErrorDetail) then
                [ pre_ [ text error.restLines ] ]
              else
                []
        )
    , a
        [ onClick $ const $ Just $ MoveToPosition error.startLineNumber error.startColumn
        , class_ underline
        ]
        [ text $ show error.startLineNumber ]
    ]

  formatError { message, startColumn, startLineNumber } =
    let
      lines' = lines message

      firstLine /\ restLines =
        if (take 12 <$> head lines') == Just "Syntax error" then
          "Syntax error" /\ (unlines $ drop 2 lines')
        else
          "Error" /\ unlines lines'
    in
      { message, startColumn, startLineNumber, firstLine, restLines }
