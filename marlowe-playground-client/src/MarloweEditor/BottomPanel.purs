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
import Halogen.Classes (aHorizontal, flexLeft, underline)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), HTML, a, button, div, li, pre, section, text, ul_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, enabled)
import MarloweEditor.Types (Action(..), BottomPanelView(..), State, _editorErrors, _editorWarnings, _showErrorDetail, contractHasErrors)
import StaticAnalysis.BottomPanel (analysisResultPane)
import StaticAnalysis.Types (_analysisState, isCloseAnalysisLoading, isReachabilityLoading, isStaticLoading)
import Text.Parsing.StringParser.Basic (lines)

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state StaticAnalysisView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents ]
    ]
    [ analysisResultPane state
    , button [ onClick $ const $ Just $ AnalyseContract, enabled enabled', classes (if enabled' then [ ClassName "analyse-btn" ] else [ ClassName "analyse-btn", ClassName "disabled" ]) ]
        [ text (if loading then "Analysing..." else "Analyse for warnings") ]
    , button [ onClick $ const $ Just $ AnalyseReachabilityContract, enabled enabled', classes (if enabled' then [ ClassName "analyse-btn" ] else [ ClassName "analyse-btn", ClassName "disabled" ]) ]
        [ text (if loadingReachability then "Analysing..." else "Analyse reachability") ]
    , button [ onClick $ const $ Just $ AnalyseContractForCloseRefund, enabled enabled', classes (if enabled' then [ ClassName "analyse-btn" ] else [ ClassName "analyse-btn", ClassName "disabled" ]) ]
        [ text (if loadingCloseAnalysis then "Analysing..." else "Analyse for refunds on Close") ]
    ]
  where
  loading = state ^. _analysisState <<< to isStaticLoading

  loadingReachability = state ^. _analysisState <<< to isReachabilityLoading

  loadingCloseAnalysis = state ^. _analysisState <<< to isCloseAnalysisLoading

  enabled' = not loading && not loadingReachability && not loadingCloseAnalysis && not contractHasErrors state

panelContents state MarloweWarningsView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents, flexLeft ]
    ]
    content
  where
  warnings = state ^. _editorWarnings

  content =
    if Array.null warnings then
      [ pre [ class_ (ClassName "error-content") ] [ text "No warnings" ] ]
    else
      [ div [ classes [ ClassName "error-headers", ClassName "error-row" ] ]
          [ div [] [ text "Description" ]
          , div [] [ text "Line Number" ]
          ]
      , ul_ (map renderWarning warnings)
      ]

  renderWarning warning =
    li [ classes [ ClassName "error-row" ] ]
      [ text warning.message
      , a
          [ onClick $ const $ Just $ MoveToPosition warning.startLineNumber warning.startColumn
          , class_ underline
          ]
          [ text $ show warning.startLineNumber ]
      ]

panelContents state MarloweErrorsView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents, flexLeft ]
    ]
    content
  where
  errors = state ^. (_editorErrors <<< to (map formatError))

  content =
    if Array.null errors then
      [ pre [ class_ (ClassName "error-content") ] [ text "No errors" ] ]
    else
      [ div [ classes [ ClassName "error-headers", ClassName "error-row" ] ]
          [ div [] [ text "Description" ]
          , div [] [ text "Line Number" ]
          ]
      , ul_ (map renderError errors)
      ]

  renderError error =
    li [ classes [ ClassName "error-row", ClassName "flex-wrap" ] ]
      ( [ a [ onClick $ const $ Just $ ShowErrorDetail (state ^. (_showErrorDetail <<< to not)) ]
            [ text $ (if state ^. _showErrorDetail then "- " else "+ ") <> error.firstLine ]
        , a
            [ onClick $ const $ Just $ MoveToPosition error.startLineNumber error.startColumn
            , class_ underline
            ]
            [ text $ show error.startLineNumber ]
        ]
          <> if (state ^. _showErrorDetail) then
              [ pre [ class_ (ClassName "error-content") ] [ text error.restLines ] ]
            else
              []
      )

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
