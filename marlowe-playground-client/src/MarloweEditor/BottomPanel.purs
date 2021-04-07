module MarloweEditor.BottomPanel
  ( panelContents
  ) where

import Prelude hiding (div)
import BottomPanel.View (metadataList)
import Data.Array (concat, drop, head)
import Data.Array as Array
import Data.Lens (to, (^.))
import Data.Maybe (Maybe(..))
import Data.String (take)
import Data.String.Extra (unlines)
import Data.Tuple.Nested ((/\))
import Halogen.Classes (flex, flexCol, fontBold, fullWidth, grid, gridColsDescriptionLocation, justifySelfEnd, minW0, overflowXScroll, paddingRight, underline)
import Halogen.HTML (ClassName(..), HTML, a, div, div_, input, option, pre_, section, section_, select, span_, text)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (InputType(..), class_, classes, placeholder, selected, type_, value)
import Marlowe.Extended (contractTypeArray, contractTypeName, contractTypeInitials, initialsToContractType)
import Marlowe.Extended.Metadata (MetaData, _choiceDescriptions, _choiceNames, _roleDescriptions, _roles, _slotParameterDescriptions, _slotParameters, _valueParameterDescriptions, _valueParameters)
import MarloweEditor.Types (Action(..), BottomPanelView(..), MetadataAction(..), State, _editorErrors, _editorWarnings, _hasHoles, _metadataHintInfo, _showErrorDetail, contractHasErrors)
import StaticAnalysis.BottomPanel (analysisResultPane, analyzeButton, clearButton)
import StaticAnalysis.Types (_analysisExecutionState, _analysisState, isCloseAnalysisLoading, isNoneAsked, isReachabilityLoading, isStaticLoading)
import Text.Parsing.StringParser.Basic (lines)

panelContents :: forall p. State -> MetaData -> BottomPanelView -> HTML p Action
panelContents state metadata MetadataView =
  div [ classes [ ClassName "metadata-form" ] ]
    ( concat
        [ [ div [ class_ $ ClassName "metadata-mainprop-label" ]
              [ text "Contract type: " ]
          , div [ class_ $ ClassName "metadata-mainprop-edit" ]
              [ select
                  [ class_ $ ClassName "metadata-input"
                  , onValueChange $ Just <<< MetadataAction <<< SetContractType <<< initialsToContractType
                  ] do
                  ct <- contractTypeArray
                  pure
                    $ option
                        [ value $ contractTypeInitials ct
                        , selected (ct == metadata.contractType)
                        ]
                        [ text $ contractTypeName ct
                        ]
              ]
          ]
        , [ div [ class_ $ ClassName "metadata-mainprop-label" ]
              [ text "Contract name: " ]
          , div [ class_ $ ClassName "metadata-mainprop-edit" ]
              [ input
                  [ type_ InputText
                  , placeholder "Contract name"
                  , class_ $ ClassName "metadata-input"
                  , value metadata.contractName
                  , onValueChange $ Just <<< MetadataAction <<< SetContractName
                  ]
              ]
          ]
        , [ div [ class_ $ ClassName "metadata-mainprop-label" ]
              [ text "Contract description: " ]
          , div [ class_ $ ClassName "metadata-mainprop-edit" ]
              [ input
                  [ type_ InputText
                  , placeholder "Contract description"
                  , class_ $ ClassName "metadata-input"
                  , value metadata.contractDescription
                  , onValueChange $ Just <<< MetadataAction <<< SetContractDescription
                  ]
              ]
          ]
        , generateMetadataList _roleDescriptions _roles SetRoleDescription DeleteRoleDescription "Role" "role"
        , generateMetadataList _choiceDescriptions _choiceNames SetChoiceDescription DeleteChoiceDescription "Choice" "choice"
        , generateMetadataList _slotParameterDescriptions _slotParameters SetSlotParameterDescription DeleteSlotParameterDescription "Slot parameter" "slot parameter"
        , generateMetadataList _valueParameterDescriptions _valueParameters SetValueParameterDescription DeleteValueParameterDescription "Value parameter" "value parameter"
        ]
    )
  where
  generateMetadataList mapLens setLens = metadataList MetadataAction (metadata ^. mapLens) (state ^. (_metadataHintInfo <<< setLens))

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

  analysisEnabled = nothingLoading && not contractHasErrors state

panelContents state _ MarloweWarningsView =
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

panelContents state _ MarloweErrorsView =
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
