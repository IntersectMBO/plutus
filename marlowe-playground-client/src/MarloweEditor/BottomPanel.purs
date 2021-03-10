module MarloweEditor.BottomPanel
  ( panelContents
  ) where

import Prelude hiding (div)
import Data.Array (drop, head)
import Data.Array as Array
import Data.Lens (to, (^.))
import Data.List (List)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (toUnfoldable)
import Data.String (take)
import Data.String.Extra (unlines)
import Data.Tuple.Nested (type (/\), (/\))
import Foreign.Generic (encodeJSON)
import Halogen.Classes (flex, flexCol, fontBold, fullWidth, grid, gridColsDescriptionLocation, justifySelfEnd, minW0, minusBtn, overflowXScroll, paddingRight, plusBtn, smallBtn, underline)
import Halogen.HTML (ClassName(..), HTML, a, button, div, div_, em_, h6_, input, li_, ol_, option, pre_, section, section_, select, span, span_, text)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (InputType(..), class_, classes, placeholder, selected, type_, value)
import Marlowe.Extended (MetaData, _choiceNames, contractTypeArray, contractTypeName, contractTypeInitials, initialsToContractType)
import Marlowe.Semantics as S
import MarloweEditor.Types (Action(..), BottomPanelView(..), MetadataAction(..), State, _editorErrors, _editorWarnings, _hasHoles, _metadataHintInfo, _showErrorDetail, contractHasErrors)
import StaticAnalysis.BottomPanel (analysisResultPane, analyzeButton, clearButton)
import StaticAnalysis.Types (_analysisExecutionState, _analysisState, isCloseAnalysisLoading, isNoneAsked, isReachabilityLoading, isStaticLoading)
import Text.Parsing.StringParser.Basic (lines)

panelContents :: forall p. State -> MetaData -> BottomPanelView -> HTML p Action
panelContents state metadata MetadataView =
  div [ classes [ ClassName "padded-explanation" ] ]
    [ div [ class_ $ ClassName "metadata-field-group" ]
        [ text "Contract type: "
        , select
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
    , div [ class_ $ ClassName "metadata-field-group" ]
        [ text "Contract name: "
        , input
            [ type_ InputText
            , placeholder "Contract name"
            , class_ $ ClassName "metadata-input"
            , value metadata.contractName
            , onValueChange $ Just <<< MetadataAction <<< SetContractName
            ]
        ]
    , div [ class_ $ ClassName "metadata-field-group" ]
        [ text "Contract description: "
        , input
            [ type_ InputText
            , placeholder "Contract description"
            , class_ $ ClassName "metadata-input"
            , value metadata.contractDescription
            , onValueChange $ Just <<< MetadataAction <<< SetContractDescription
            ]
        ]
    , div [ class_ $ ClassName "metadata-field-group" ]
        if Map.isEmpty choiceMap then
          []
        else
          [ h6_ [ em_ [ text "Choice descriptions" ] ]
          , ol_
              $ map
                  ( \(key /\ val) ->
                      li_
                        ( case val of
                            Just (desc /\ needed) ->
                              [ text $ "Choice " <> show key <> ": "
                              , input
                                  [ type_ InputText
                                  , placeholder $ "Description for choice " <> show key
                                  , class_ $ ClassName "metadata-input"
                                  , value desc
                                  , onValueChange $ Just <<< MetadataAction <<< SetChoiceDescription key
                                  ]
                              , button
                                  [ classes [ minusBtn, smallBtn, ClassName "align-top" ]
                                  , onClick $ const $ Just $ MetadataAction $ DeleteChoiceDescription key
                                  ]
                                  [ text "-" ]
                              ]
                                <> if needed then [] else [ span [ classes [ ClassName "metadata-error", ClassName "metadata-not-used" ] ] [ text "Not used" ] ]
                            Nothing ->
                              [ span [ class_ (ClassName "metadata-error") ] [ text $ "Choice " <> show key <> " description not defined" ]
                              , button
                                  [ classes [ plusBtn, smallBtn, ClassName "align-top" ]
                                  , onClick $ const $ Just $ MetadataAction $ SetChoiceDescription key mempty
                                  ]
                                  [ text "+" ]
                              ]
                        )
                  )
              $ Map.toUnfoldable choiceMap
          ]
    , div_ [ text (encodeJSON metadata) ]
    , div_ [ text (show (state ^. _metadataHintInfo)) ]
    ]
  where
  mergeMaps :: (Maybe (String /\ Boolean)) -> (Maybe (String /\ Boolean)) -> (Maybe (String /\ Boolean))
  mergeMaps (Just (x /\ _)) _ = Just (x /\ true)

  mergeMaps _ _ = Nothing

  choiceMap :: Map S.TokenName (Maybe (String /\ Boolean))
  choiceMap =
    Map.unionWith mergeMaps
      (map (\x -> Just (x /\ false)) metadata.choiceDescriptions)
      (Map.fromFoldable (map (\x -> x /\ Nothing) ((toUnfoldable (state ^. (_metadataHintInfo <<< _choiceNames))) :: List String)))

panelContents state _ StaticAnalysisView =
  section [ classes [ flex, flexCol ] ]
    if (state ^. _hasHoles) then
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
