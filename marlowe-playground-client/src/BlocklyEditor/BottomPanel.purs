module BlocklyEditor.BottomPanel
  ( panelContents
  ) where

import Prelude hiding (div)
import BlocklyEditor.Types (Action(..), BottomPanelView(..), State)
import Data.Array (drop, head)
import Data.Array as Array
import Data.Lens (to, (^.))
import Data.Maybe (Maybe(..))
import Data.String (take)
import Data.String.Extra (unlines)
import Data.Tuple.Nested ((/\))
import Halogen.Classes (aHorizontal, flex, flexCol, flexLeft, paddingRight, underline)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), HTML, a, div, div_, li, pre, section, text, ul_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import StaticAnalysis.BottomPanel (analysisResultPane, analyzeButton, clearButton)
import StaticAnalysis.Types (_analysisExecutionState, _analysisState, isCloseAnalysisLoading, isNoneAsked, isReachabilityLoading, isStaticLoading)
import Text.Parsing.StringParser.Basic (lines)

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state StaticAnalysisView =
  section [ classes [ flex, flexCol ] ]
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

  analysisEnabled = nothingLoading

panelContents state BlocklyWarningsView =
  section
    [ classes []
    ]
    content
  where
  -- warnings = state ^. _editorWarnings
  content = [ div_ [ text "Warning pane" ] ]

{- if Array.null warnings then
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
  -}
