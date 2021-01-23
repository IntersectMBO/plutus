module MarloweEditor.BottomPanel (bottomPanel) where

import Prelude hiding (div)
import Data.Array (drop, head, length)
import Data.Array as Array
import Data.Foldable (foldMap)
import Data.Lens (to, (^.))
import Data.List (List, null, toUnfoldable)
import Data.List as List
import Data.List.NonEmpty (toList)
import Data.Maybe (Maybe(..))
import Data.String (take)
import Data.String.Extra (unlines)
import Data.Tuple.Nested ((/\))
import Halogen.Classes (aHorizontal, accentBorderBottom, active, activeClass, closeDrawerArrowIcon, collapsed, flex, flexLeft, flexTen, footerPanelBg, minimizeIcon, spanText, underline)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), HTML, a, a_, b_, br_, button, div, h2, h3, img, li, li_, ol, pre, section, span_, text, ul, ul_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, class_, classes, enabled, src)
import Marlowe.Semantics (ChoiceId(..), Input(..), Payee(..), Slot(..), SlotInterval(..), TransactionInput(..), TransactionWarning(..))
import Marlowe.Symbolic.Types.Response as R
import MarloweEditor.Types (Action(..), AnalysisState(..), BottomPanelView(..), MultiStageAnalysisData(..), State, _analysisState, _bottomPanelView, _editorErrors, _editorWarnings, _showBottomPanel, _showErrorDetail, contractHasErrors)
import Network.RemoteData (RemoteData(..), isLoading)
import Pretty (showPrettyToken)
import Servant.PureScript.Ajax (AjaxError(..), ErrorDescription(..))
import Text.Parsing.StringParser.Basic (lines)

bottomPanel :: forall p. State -> HTML p Action
bottomPanel state =
  div
    ( [ classes
          ( if showingBottomPanel then
              [ ClassName "simulation-bottom-panel" ]
            else
              [ ClassName "simulation-bottom-panel", collapsed ]
          )
      ]
    )
    [ div [ classes [ flex, ClassName "flip-x", ClassName "full-height" ] ]
        [ div [ class_ flexTen ]
            [ div [ classes [ footerPanelBg, active ] ]
                [ section [ classes [ ClassName "panel-header", aHorizontal ] ]
                    [ div [ classes [ ClassName "panel-sub-header-main", aHorizontal, accentBorderBottom ] ]
                        [ ul [ class_ (ClassName "start-item") ]
                            [ li [ class_ (ClassName "minimize-icon-container") ]
                                [ a [ onClick $ const $ Just $ ShowBottomPanel (state ^. _showBottomPanel <<< to not) ]
                                    [ img [ classes (minimizeIcon $ state ^. _showBottomPanel), src closeDrawerArrowIcon, alt "close drawer icon" ] ]
                                ]
                            ]
                        , ul [ classes [ ClassName "demo-list", aHorizontal ] ]
                            [ li
                                [ classes ([] <> isActive StaticAnalysisView)
                                , onClick $ const $ Just $ ChangeBottomPanelView StaticAnalysisView
                                ]
                                [ a_ [ text "Static Analysis" ] ]
                            , li
                                [ classes ([] <> isActive MarloweWarningsView)
                                , onClick $ const $ Just $ ChangeBottomPanelView MarloweWarningsView
                                ]
                                [ a_ [ text $ "Warnings" <> if Array.null warnings then "" else " (" <> show (length warnings) <> ")" ] ]
                            , li
                                [ classes ([] <> isActive MarloweErrorsView)
                                , onClick $ const $ Just $ ChangeBottomPanelView MarloweErrorsView
                                ]
                                [ a_ [ text $ "Errors" <> if Array.null errors then "" else " (" <> show (length errors) <> ")" ] ]
                            ]
                        ]
                    ]
                , panelContents state (state ^. _bottomPanelView)
                ]
            ]
        ]
    ]
  where
  isActive view = state ^. _bottomPanelView <<< (activeClass (eq view))

  warnings = state ^. _editorWarnings

  errors = state ^. _editorErrors

  showingBottomPanel = state ^. _showBottomPanel

isStaticLoading :: AnalysisState -> Boolean
isStaticLoading (WarningAnalysis remoteData) = isLoading remoteData

isStaticLoading _ = false

isReachabilityLoading :: AnalysisState -> Boolean
isReachabilityLoading (ReachabilityAnalysis (AnalysisInProgress _)) = true

isReachabilityLoading _ = false

isCloseAnalysisLoading :: AnalysisState -> Boolean
isCloseAnalysisLoading (CloseAnalysis (AnalysisInProgress _)) = true

isCloseAnalysisLoading _ = false

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

analysisResultPane :: forall p. State -> HTML p Action
analysisResultPane state =
  let
    result = state ^. _analysisState

    explanation = div [ classes [ ClassName "padded-explanation" ] ]
  in
    case result of
      NoneAsked ->
        explanation
          [ text ""
          ]
      WarningAnalysis staticSubResult -> case staticSubResult of
        NotAsked ->
          explanation
            [ text ""
            ]
        Success (R.Valid) ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Warning Analysis Result: Pass" ]
            , text "Static analysis could not find any execution that results in any warning."
            ]
        Success (R.CounterExample { initialSlot, transactionList, transactionWarning }) ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Warning Analysis Result: Warnings Found" ]
            , text "Static analysis found the following counterexample:"
            , ul [ classes [ ClassName "indented-enum-initial" ] ]
                [ li_
                    [ spanText "Warnings issued: "
                    , displayWarningList transactionWarning
                    ]
                , li_
                    [ spanText "Initial slot: "
                    , b_ [ spanText (show initialSlot) ]
                    ]
                , li_
                    [ spanText "Offending transaction list: "
                    , displayTransactionList transactionList
                    ]
                ]
            ]
        Success (R.Error str) ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Error during warning analysis" ]
            , text "Analysis failed for the following reason:"
            , ul [ classes [ ClassName "indented-enum-initial" ] ]
                [ li_
                    [ b_ [ spanText str ]
                    ]
                ]
            ]
        Failure (AjaxError { description }) ->
          let
            err = case description of
              DecodingError e -> "Decoding error: " <> e
              ConnectionError e -> "Connection error: " <> e
              NotFound -> "Data not found."
              ResponseError status body -> "Response error: " <> show status <> " " <> body
              ResponseFormatError e -> "Response Format error: " <> e
          in
            explanation
              [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Error during warning analysis" ]
              , text "Analysis failed for the following reason:"
              , ul [ classes [ ClassName "indented-enum-initial" ] ]
                  [ li_
                      [ b_ [ spanText err ]
                      ]
                  ]
              ]
        Loading -> text ""
      ReachabilityAnalysis reachabilitySubResult -> case reachabilitySubResult of
        AnalysisNotStarted ->
          explanation
            [ text ""
            ]
        AnalysisInProgress
          { numSubproblems: totalSteps
        , numSolvedSubproblems: doneSteps
        , counterExampleSubcontracts: foundcounterExampleSubcontracts
        } ->
          explanation
            ( [ text ("Reachability analysis in progress, " <> show doneSteps <> " subcontracts out of " <> show totalSteps <> " analysed...") ]
                <> if null foundcounterExampleSubcontracts then
                    [ br_, text "No unreachable subcontracts found so far." ]
                  else
                    ( [ br_, text "Found the following unreachable subcontracts so far:" ]
                        <> [ ul [ classes [ ClassName "indented-enum-initial" ] ] do
                              contractPath <- toUnfoldable foundcounterExampleSubcontracts
                              pure (li_ [ text (show contractPath) ])
                          ]
                    )
            )
        AnalyisisFailure err ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Error during reachability analysis" ]
            , text "Reachability analysis failed for the following reason:"
            , ul [ classes [ ClassName "indented-enum-initial" ] ]
                [ li_
                    [ b_ [ spanText err ]
                    ]
                ]
            ]
        AnalysisFoundCounterExamples { counterExampleSubcontracts } ->
          explanation
            ( [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Reachability Analysis Result: Unreachable Subcontract Found" ]
              , text "Static analysis found the following subcontracts that are unreachable:"
              ]
                <> [ ul [ classes [ ClassName "indented-enum-initial" ] ] do
                      contractPath <- toUnfoldable (toList counterExampleSubcontracts)
                      pure (li_ [ text (show contractPath) ])
                  ]
            )
        AnalysisFinishedAndPassed ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Reachability Analysis Result: Pass" ]
            , text "Reachability analysis could not find any subcontract that is not reachable."
            ]
      CloseAnalysis closeAnalysisSubResult -> case closeAnalysisSubResult of
        AnalysisNotStarted ->
          explanation
            [ text ""
            ]
        AnalysisInProgress
          { numSubproblems: totalSteps
        , numSolvedSubproblems: doneSteps
        , counterExampleSubcontracts: foundcounterExampleSubcontracts
        } ->
          explanation
            ( [ text ("Close analysis in progress, " <> show doneSteps <> " subcontracts out of " <> show totalSteps <> " analysed...") ]
                <> if null foundcounterExampleSubcontracts then
                    [ br_, text "No refunds on Close found so far." ]
                  else
                    ( [ br_, text "Found the following refunds on Close so far:" ]
                        <> [ ul [ classes [ ClassName "indented-enum-initial" ] ] do
                              contractPath <- toUnfoldable foundcounterExampleSubcontracts
                              pure (li_ [ text (show contractPath) ])
                          ]
                    )
            )
        AnalyisisFailure err ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Error during Close refund analysis" ]
            , text "Close refund analysis failed for the following reason:"
            , ul [ classes [ ClassName "indented-enum-initial" ] ]
                [ li_
                    [ b_ [ spanText err ]
                    ]
                ]
            ]
        AnalysisFoundCounterExamples { counterExampleSubcontracts } ->
          explanation
            ( [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Close Refund Analysis Result: Some of the Close constructs may refund assets" ]
              , text "The following Close constructs may implicitly refund money:"
              ]
                <> [ ul [ classes [ ClassName "indented-enum-initial" ] ] do
                      contractPath <- toUnfoldable (toList counterExampleSubcontracts)
                      pure (li_ [ text (show contractPath) ])
                  ]
                <> [ text "This does not necessarily mean there is anything wrong with the contract." ]
            )
        AnalysisFinishedAndPassed ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Close Refund Analysis Result: No implicit refunds" ]
            , text "None of the Close constructs refunds any money, all refunds are explicit."
            ]

displayTransactionList :: forall p. Array TransactionInput -> HTML p Action
displayTransactionList transactionList =
  ol [ classes [ ClassName "indented-enum" ] ]
    ( do
        ( TransactionInput
            { interval: SlotInterval (Slot from) (Slot to)
          , inputs: inputList
          }
        ) <-
          transactionList
        pure
          ( li_
              [ span_
                  [ b_ [ text "Transaction" ]
                  , text " with slot interval "
                  , b_ [ text $ (show from <> " to " <> show to) ]
                  , if List.null inputList then
                      text " and no inputs (empty transaction)."
                    else
                      text " and inputs:"
                  ]
              , if List.null inputList then
                  text ""
                else
                  displayInputList inputList
              ]
          )
    )

displayInputList :: forall p. List Input -> HTML p Action
displayInputList inputList =
  ol [ classes [ ClassName "indented-loweralpha-enum" ] ]
    ( do
        input <- (toUnfoldable inputList)
        pure (li_ (displayInput input))
    )

displayInput :: forall p i. Input -> Array (HTML p i)
displayInput (IDeposit owner party tok money) =
  [ b_ [ text "IDeposit" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " deposits "
  , b_ [ text $ show money ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " into account of "
  , b_ [ text (show owner) ]
  , text "."
  ]

displayInput (IChoice (ChoiceId choiceId party) chosenNum) =
  [ b_ [ text "IChoice" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " chooses number "
  , b_ [ text $ show chosenNum ]
  , text " for choice "
  , b_ [ text $ show choiceId ]
  , text "."
  ]

displayInput (INotify) =
  [ b_ [ text "INotify" ]
  , text " - The contract is notified that an observation became "
  , b_ [ text "True" ]
  ]

displayWarningList :: forall p. Array TransactionWarning -> HTML p Action
displayWarningList transactionWarnings =
  ol [ classes [ ClassName "indented-enum" ] ]
    ( do
        warning <- transactionWarnings
        pure (li_ (displayWarning warning))
    )

displayWarnings :: forall p. Array TransactionWarning -> HTML p Action
displayWarnings [] = text mempty

displayWarnings warnings =
  div
    [ classes
        [ ClassName "invalid-transaction"
        , ClassName "input-composer"
        ]
    ]
    [ h2 [] [ text "Warnings" ]
    , ol
        []
        $ foldMap (\warning -> [ li_ (displayWarning warning) ]) warnings
    ]

displayWarning :: forall p. TransactionWarning -> Array (HTML p Action)
displayWarning (TransactionNonPositiveDeposit party owner tok amount) =
  [ b_ [ text "TransactionNonPositiveDeposit" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " is asked to deposit "
  , b_ [ text $ show amount ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " into account of "
  , b_ [ text (show owner) ]
  , text "."
  ]

displayWarning (TransactionNonPositivePay owner payee tok amount) =
  [ b_ [ text "TransactionNonPositivePay" ]
  , text " - The contract is supposed to make a payment of "
  , b_ [ text $ show amount ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " from account of "
  , b_ [ text (show owner) ]
  , text " to "
  , b_
      [ text case payee of
          (Account owner2) -> ("account of " <> (show owner2))
          (Party dest) -> ("party " <> (show dest))
      ]
  , text "."
  ]

displayWarning (TransactionPartialPay owner payee tok amount expected) =
  [ b_ [ text "TransactionPartialPay" ]
  , text " - The contract is supposed to make a payment of "
  , b_ [ text $ show expected ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " from account of "
  , b_ [ text (show owner) ]
  , text " to "
  , b_
      [ text case payee of
          (Account owner2) -> ("account of " <> (show owner2))
          (Party dest) -> ("party " <> (show dest))
      ]
  , text " but there is only "
  , b_ [ text $ show amount ]
  , text "."
  ]

displayWarning (TransactionShadowing valId oldVal newVal) =
  [ b_ [ text "TransactionShadowing" ]
  , text " - The contract defined the value with id "
  , b_ [ text (show valId) ]
  , text " before, it was assigned the value "
  , b_ [ text (show oldVal) ]
  , text " and now it is being assigned the value "
  , b_ [ text (show newVal) ]
  , text "."
  ]

displayWarning TransactionAssertionFailed =
  [ b_ [ text "TransactionAssertionFailed" ]
  , text " - An assertion in the contract did not hold."
  ]
