module BlocklyEditor.BottomPanel
  ( panelContents
  ) where

import Prelude hiding (div)
import BlocklyEditor.Types (Action(..), BottomPanelView(..), State, _hasHoles, _metadataHintInfo, _warnings)
import BottomPanel.View (metadataView)
import Data.Array as Array
import Data.Lens (to, (^.))
import Data.Maybe (Maybe(..))
import Halogen.Classes (flex, flexCol, fontBold, fullWidth, grid, gridColsDescriptionLocation, justifySelfEnd, paddingRight, underline)
import Halogen.HTML (HTML, a, div, div_, pre_, section, section_, span_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import Marlowe.Extended.Metadata (MetaData)
import StaticAnalysis.BottomPanel (analysisResultPane, analyzeButton, clearButton)
import StaticAnalysis.Types (_analysisExecutionState, _analysisState, isCloseAnalysisLoading, isNoneAsked, isReachabilityLoading, isStaticLoading)

panelContents :: forall p. State -> MetaData -> BottomPanelView -> HTML p Action
panelContents state metadata MetadataView = metadataView (state ^. _metadataHintInfo) metadata MetadataAction

panelContents state metadata StaticAnalysisView =
  section [ classes [ flex, flexCol ] ]
    if (state ^. _hasHoles) then
      [ div_ [ text "The contract needs to be complete (no holes) before doing static analysis." ]
      ]
    else
      [ analysisResultPane metadata SetIntegerTemplateParam state
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

panelContents state _ BlocklyWarningsView =
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
