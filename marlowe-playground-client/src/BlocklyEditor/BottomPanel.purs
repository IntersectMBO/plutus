module BlocklyEditor.BottomPanel
  ( panelContents
  ) where

import Prelude hiding (div)
import BlocklyEditor.Types (Action(..), BottomPanelView(..), State, _warnings)
import Data.Array as Array
import Data.Lens (to, (^.))
import Data.Maybe (Maybe(..))
import Halogen.Classes (flex, flexCol, fontBold, fullWidth, grid, gridColsDescriptionLocation, justifySelfEnd, paddingRight, underline)
import Halogen.HTML (HTML, a, div, pre_, section, section_, span_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import StaticAnalysis.BottomPanel (analysisResultPane, analyzeButton, clearButton)
import StaticAnalysis.Types (_analysisExecutionState, _analysisState, isCloseAnalysisLoading, isNoneAsked, isReachabilityLoading, isStaticLoading)

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
  section_
    if Array.null warnings then
      [ pre_ [ text "No warnings" ] ]
    else
      [ div [ classes [ grid, gridColsDescriptionLocation, fullWidth ] ]
          (headers <> (renderWarning =<< warnings))
      ]
  where
  warnings = state ^. _warnings

  headers =
    [ div [ class_ fontBold ] [ text "Description" ]
    , div [ class_ fontBold ] [ text "Location" ]
    ]

  renderWarning warning =
    [ span_ $ [ text $ show warning ]
    , a
        [ onClick $ const $ Just $ SelectWarning warning
        , classes [ underline, justifySelfEnd ]
        ]
        [ text $ "select block" ]
    ]
