module Simulation.BottomPanel where

import Control.Alternative (map)
import Data.Array (concatMap, drop, fold, head, length, reverse)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Eq (eq, (==))
import Data.Foldable (foldMap)
import Data.HeytingAlgebra (not, (||))
import Data.Lens (to, traversed, (^.), (^..))
import Data.Lens.NonEmptyList (_Head)
import Data.List (List, toUnfoldable)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.String (take)
import Data.String.Extra (unlines)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Halogen.Classes (aHorizontal, accentBorderBottom, active, activeClass, closeDrawerArrowIcon, first, flex, flexLeft, flexTen, minimizeIcon, rTable, rTable6cols, rTableCell, rTableDataRow, rTableEmptyRow, spanText, underline)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), HTML, a, a_, b_, button, code_, div, h2, h3, img, li, li_, ol, pre, section, span_, strong_, text, ul)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, class_, classes, enabled, src)
import Marlowe.Parser (transactionInputList, transactionWarningList)
import Marlowe.Semantics (AccountId(..), Assets(..), ChoiceId(..), Input(..), Payee(..), Payment(..), Slot(..), SlotInterval(..), Token(..), TransactionInput(..), TransactionWarning(..), ValueId(..), _accounts, _boundValues, _choices, maxTime)
import Marlowe.Symbolic.Types.Response as R
import Network.RemoteData (RemoteData(..), isLoading)
import Prelude (bind, const, mempty, pure, show, zero, ($), (&&), (<$>), (<<<), (<>))
import Simulation.Types (Action(..), BottomPanelView(..), State, _analysisState, _bottomPanelView, _marloweState, _showBottomPanel, _showErrorDetail, isContractValid)
import Simulation.State (_contract, _currentTransactionInput, _editorErrors, _editorWarnings, _payments, _slot, _state, _transactionError, _transactionWarnings)
import Text.Parsing.StringParser (runParser)
import Text.Parsing.StringParser.Basic (lines)

simulationBottomPanel :: State -> Array ClassName
simulationBottomPanel state = if state ^. _showBottomPanel then [ ClassName "simulation-bottom-panel" ] else [ ClassName "simulation-bottom-panel", ClassName "collapse" ]

footerPanelBg :: Boolean -> Array ClassName
footerPanelBg display =
  if display then
    [ ClassName "footer-panel-bg", ClassName "expanded" ]
  else
    [ ClassName "footer-panel-bg" ]

bottomPanel :: forall p. State -> HTML p Action
bottomPanel state =
  div [ classes (simulationBottomPanel state) ]
    [ div [ class_ flex ]
        [ div [ class_ flexTen ]
            [ div [ classes (footerPanelBg (state ^. _showBottomPanel) <> [ active ]) ]
                [ section [ classes [ ClassName "panel-header", aHorizontal ] ]
                    [ div [ classes ([ ClassName "panel-sub-header-main", aHorizontal ] <> (if state ^. _showBottomPanel then [ accentBorderBottom ] else [])) ]
                        [ ul [ class_ (ClassName "start-item") ]
                            [ li [ class_ (ClassName "minimize-icon-container") ]
                                [ a [ onClick $ const $ Just $ ShowBottomPanel (state ^. _showBottomPanel <<< to not) ]
                                    [ img [ classes (minimizeIcon $ state ^. _showBottomPanel), src closeDrawerArrowIcon, alt "close drawer icon" ] ]
                                ]
                            ]
                        , ul [ classes [ ClassName "demo-list", aHorizontal ] ]
                            [ li
                                [ classes ((if hasRuntimeWarnings || hasRuntimeError then [ ClassName "error-tab" ] else []) <> isActive CurrentStateView)
                                , onClick $ const $ Just $ ChangeSimulationView CurrentStateView
                                ]
                                [ a_ [ text "Current State" ] ]
                            , li
                                [ classes ([] <> isActive StaticAnalysisView)
                                , onClick $ const $ Just $ ChangeSimulationView StaticAnalysisView
                                ]
                                [ a_ [ text "Static Analysis" ] ]
                            , li
                                [ classes ([] <> isActive MarloweWarningsView)
                                , onClick $ const $ Just $ ChangeSimulationView MarloweWarningsView
                                ]
                                [ a_ [ text $ "Warnings" <> if Array.null warnings then "" else " (" <> show (length warnings) <> ")" ] ]
                            , li
                                [ classes ([] <> isActive MarloweErrorsView)
                                , onClick $ const $ Just $ ChangeSimulationView MarloweErrorsView
                                ]
                                [ a_ [ text $ "Errors" <> if Array.null errors then "" else " (" <> show (length errors) <> ")" ] ]
                            , li
                                [ classes ([] <> isActive MarloweLogView)
                                , onClick $ const $ Just $ ChangeSimulationView MarloweLogView
                                ]
                                [ a_ [ text $ "Logs" ] ]
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

  warnings = state ^. (_marloweState <<< _Head <<< _editorWarnings)

  errors = state ^. (_marloweState <<< _Head <<< _editorErrors)

  hasRuntimeWarnings = state ^. (_marloweState <<< _Head <<< _transactionWarnings <<< to Array.null <<< to not)

  hasRuntimeError = state ^. (_marloweState <<< _Head <<< _transactionError <<< to isJust)

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state CurrentStateView =
  div [ class_ Classes.panelContents ]
    [ div [ classes [ rTable, rTable6cols, ClassName "panel-table" ] ]
        ( warningsRow <> errorRow
            <> dataRow "Current Block" (state ^. (_marloweState <<< _Head <<< _slot <<< to show))
            <> dataRow "Expiration Block" (state ^. (_marloweState <<< _Head <<< _contract <<< to contractMaxTime))
            <> tableRow
                { title: "Accounts"
                , emptyMessage: "No accounts have been used"
                , columns: ("Account ID" /\ "Participant" /\ "Currency Symbol" /\ "Token Name" /\ "Money")
                , rowData: accountsData
                }
            <> tableRow
                { title: "Choices"
                , emptyMessage: "No Choices have been made"
                , columns: ("Choice ID" /\ "Participant" /\ "Chosen Value" /\ mempty /\ mempty)
                , rowData: choicesData
                }
            <> tableRow
                { title: "Payments"
                , emptyMessage: "No payments have been recorded"
                , columns: ("Party" /\ "Currency Symbol" /\ "Token Name" /\ "Money" /\ mempty)
                , rowData: paymentsData
                }
            <> tableRow
                { title: "Let Bindings"
                , emptyMessage: "No values have been bound"
                , columns: ("Identifier" /\ "Value" /\ mempty /\ mempty /\ mempty)
                , rowData: bindingsData
                }
        )
    ]
  where
  contractMaxTime Nothing = "Closed"

  contractMaxTime (Just contract) = let t = maxTime contract in if t == zero then "Closed" else show t

  warnings = state ^. (_marloweState <<< _Head <<< _transactionWarnings)

  warningsRow =
    if Array.null warnings then
      []
    else
      (headerRow "Warnings" ("type" /\ "details" /\ mempty /\ mempty /\ mempty)) <> foldMap displayWarning' warnings

  error = state ^. (_marloweState <<< _Head <<< _transactionError)

  errorRow =
    if isNothing error then
      []
    else
      (headerRow "Errors" ("details" /\ mempty /\ mempty /\ mempty /\ mempty)) <> displayError error

  displayError Nothing = []

  displayError (Just err) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ classes [ rTableCell, ClassName "Rtable-single-column-row" ] ] [ text $ show err ]
    ]

  accountsData =
    let
      (accounts :: Array _) = state ^. (_marloweState <<< _Head <<< _state <<< _accounts <<< to Map.toUnfoldable)

      asTuple (Tuple (Tuple (AccountId accountNumber accountOwner) (Token currSym tokName)) value) = show accountNumber /\ show accountOwner /\ show currSym /\ show tokName /\ show value
    in
      map asTuple accounts

  choicesData =
    let
      (choices :: Array _) = state ^. (_marloweState <<< _Head <<< _state <<< _choices <<< to Map.toUnfoldable)

      asTuple (Tuple (ChoiceId choiceName choiceOwner) value) = show choiceName /\ show choiceOwner /\ show value /\ mempty /\ mempty
    in
      map asTuple choices

  paymentsData =
    let
      payments = state ^. (_marloweState <<< _Head <<< _payments)

      asTuple :: Payment -> Array (String /\ String /\ String /\ String /\ String)
      asTuple (Payment party (Assets mon)) =
        concatMap
          ( \(Tuple currencySymbol tokenMap) ->
              ( map
                  ( \(Tuple tokenName value) ->
                      (show party /\ currencySymbol /\ tokenName /\ show value /\ mempty)
                  )
                  (Map.toUnfoldable tokenMap)
              )
          )
          (Map.toUnfoldable mon)
    in
      concatMap asTuple payments

  bindingsData =
    let
      (bindings :: Array _) = state ^. (_marloweState <<< _Head <<< _state <<< _boundValues <<< to Map.toUnfoldable)

      asTuple (Tuple (ValueId valueId) value) = show valueId /\ show value /\ mempty /\ mempty /\ mempty
    in
      map asTuple bindings

  tableRow { title, emptyMessage, rowData: [] } = emptyRow title emptyMessage

  tableRow { title, columns, rowData } = headerRow title columns <> foldMap (\dataTuple -> row dataTuple) rowData

  headerRow title (a /\ b /\ c /\ d /\ e) =
    [ div [ classes [ rTableCell, first, Classes.header ] ] [ text title ] ]
      <> map (\x -> div [ classes [ rTableCell, rTableCell, Classes.header ] ] [ text x ]) [ a, b, c, d, e ]

  row (a /\ b /\ c /\ d /\ e) =
    [ div [ classes [ rTableCell, first ] ] [] ]
      <> map (\x -> div [ class_ rTableCell ] [ text x ]) [ a, b, c, d, e ]

  emptyRow title message =
    [ div [ classes [ rTableCell, first, Classes.header ] ]
        [ text title ]
    , div [ classes [ rTableCell, rTableEmptyRow, Classes.header ] ] [ text message ]
    ]

  dataRow title message =
    [ div [ classes [ rTableCell, first, Classes.header ] ]
        [ text title ]
    , div [ classes [ rTableCell, rTableDataRow ] ] [ text message ]
    ]

  displayWarning' (TransactionNonPositiveDeposit party (AccountId accNum owner) tok amount) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionNonPositiveDeposit" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "Party " <> show party <> " is asked to deposit " <> show amount
            <> " units of "
            <> show tok
            <> " into account "
            <> show accNum
            <> " of "
            <> show owner
            <> "."
        ]
    ]

  displayWarning' (TransactionNonPositivePay (AccountId accNum owner) payee tok amount) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionNonPositivePay" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "The contract is supposed to make a payment of "
            <> show amount
            <> " units of "
            <> show tok
            <> " from account "
            <> show accNum
            <> " of "
            <> show owner
            <> " to "
            <> ( case payee of
                  (Account (AccountId accNum2 owner2)) -> "account " <> show accNum2 <> " of " <> show owner2
                  (Party dest) -> "party " <> show dest
              )
            <> "."
        ]
    ]

  displayWarning' (TransactionPartialPay (AccountId accNum owner) payee tok amount expected) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionPartialPay" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "The contract is supposed to make a payment of "
            <> show expected
            <> " units of "
            <> show tok
            <> " from account "
            <> show accNum
            <> " of "
            <> show owner
            <> " to "
            <> ( case payee of
                  (Account (AccountId accNum2 owner2)) -> ("account " <> show accNum2 <> " of " <> show owner2)
                  (Party dest) -> ("party " <> show dest)
              )
            <> " but there is only "
            <> show amount
            <> "."
        ]
    ]

  displayWarning' (TransactionShadowing valId oldVal newVal) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionShadowing" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "The contract defined the value with id "
            <> show valId
            <> " before, it was assigned the value "
            <> show oldVal
            <> " and now it is being assigned the value "
            <> show newVal
            <> "."
        ]
    ]

  displayWarning' TransactionAssertionFailed =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionAssertionFailed" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "An assertion in the contract did not hold." ]
    ]

panelContents state StaticAnalysisView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents ]
    ]
    [ analysisResultPane state
    , button [ onClick $ const $ Just $ AnalyseContract, enabled enabled', classes (if enabled' then [ ClassName "analyse-btn" ] else [ ClassName "analyse-btn", ClassName "disabled" ]) ]
        [ text (if loading then "Analysing..." else "Analyse") ]
    ]
  where
  loading = state ^. _analysisState <<< to isLoading

  enabled' = not loading && isContractValid state

panelContents state MarloweWarningsView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents, flexLeft ]
    ]
    content
  where
  warnings = state ^. (_marloweState <<< _Head <<< _editorWarnings)

  content =
    if Array.null warnings then
      [ pre [ class_ (ClassName "error-content") ] [ text "No warnings" ] ]
    else
      [ div [ classes [ ClassName "error-headers", ClassName "error-row" ] ]
          [ div [] [ text "Description" ]
          , div [] [ text "Line Number" ]
          ]
      , ul [] (map renderWarning warnings)
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
  errors = state ^. (_marloweState <<< _Head <<< _editorErrors <<< to (map formatError))

  content =
    if Array.null errors then
      [ pre [ class_ (ClassName "error-content") ] [ text "No errors" ] ]
    else
      [ div [ classes [ ClassName "error-headers", ClassName "error-row" ] ]
          [ div [] [ text "Description" ]
          , div [] [ text "Line Number" ]
          ]
      , ul [] (map renderError errors)
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

panelContents state MarloweLogView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents, flexLeft ]
    ]
    content
  where
  inputLines = state ^.. (_marloweState <<< traversed <<< _currentTransactionInput <<< to txInputToLines)

  content =
    [ div [ classes [ ClassName "error-headers", ClassName "error-row" ] ]
        [ div [] [ text "Action" ]
        , div [] [ text "Slot" ]
        ]
    , ul [] (reverse (fold inputLines))
    ]

analysisResultPane :: forall p. State -> HTML p Action
analysisResultPane state =
  let
    result = state ^. _analysisState

    explanation = div [ classes [ ClassName "padded-explanation" ] ]
  in
    case result of
      NotAsked ->
        explanation
          [ text ""
          ]
      Success (R.Valid) ->
        explanation
          [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Analysis Result: Pass" ]
          , text "Static analysis could not find any execution that results in any warning."
          ]
      Success (R.CounterExample { initialSlot, transactionList, transactionWarning }) ->
        explanation
          [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Analysis Result: Warnings Found" ]
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
          [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Error during analysis" ]
          , text "Analysis failed for the following reason:"
          , ul [ classes [ ClassName "indented-enum-initial" ] ]
              [ li_
                  [ b_ [ spanText str ]
                  ]
              ]
          ]
      Failure failure ->
        explanation
          [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Error during analysis" ]
          , text "Analysis failed for the following reason:"
          , ul [ classes [ ClassName "indented-enum-initial" ] ]
              [ li_
                  [ b_ [ spanText failure ]
                  ]
              ]
          ]
      Loading -> text ""

displayTransactionList :: forall p. String -> HTML p Action
displayTransactionList transactionList = case runParser transactionInputList transactionList of
  Right pTL ->
    ol [ classes [ ClassName "indented-enum" ] ]
      ( do
          ( TransactionInput
              { interval: SlotInterval (Slot from) (Slot to)
            , inputs: inputList
            }
          ) <-
            ((toUnfoldable pTL) :: Array TransactionInput)
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
  Left _ -> code_ [ text transactionList ]

displayInputList :: forall p. List Input -> HTML p Action
displayInputList inputList =
  ol [ classes [ ClassName "indented-loweralpha-enum" ] ]
    ( do
        input <- (toUnfoldable inputList)
        pure (li_ (displayInput input))
    )

displayInput :: forall p i. Input -> Array (HTML p i)
displayInput (IDeposit (AccountId accNum owner) party tok money) =
  [ b_ [ text "IDeposit" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " deposits "
  , b_ [ text $ show money ]
  , text " units of "
  , b_ [ text $ show tok ]
  , text " into account "
  , b_ [ text ((show accNum) <> " of " <> (show owner)) ]
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

displayWarningList :: forall p. String -> HTML p Action
displayWarningList transactionWarnings = case runParser transactionWarningList transactionWarnings of
  Right pWL ->
    ol [ classes [ ClassName "indented-enum" ] ]
      ( do
          warning <- ((toUnfoldable pWL) :: Array TransactionWarning)
          pure (li_ (displayWarning warning))
      )
  Left _ -> code_ [ text transactionWarnings ]

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
displayWarning (TransactionNonPositiveDeposit party (AccountId accNum owner) tok amount) =
  [ b_ [ text "TransactionNonPositiveDeposit" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " is asked to deposit "
  , b_ [ text $ show amount ]
  , text " units of "
  , b_ [ text $ show tok ]
  , text " into account "
  , b_ [ text ((show accNum) <> " of " <> (show owner)) ]
  , text "."
  ]

displayWarning (TransactionNonPositivePay (AccountId accNum owner) payee tok amount) =
  [ b_ [ text "TransactionNonPositivePay" ]
  , text " - The contract is supposed to make a payment of "
  , b_ [ text $ show amount ]
  , text " units of "
  , b_ [ text $ show tok ]
  , text " from account "
  , b_ [ text ((show accNum) <> " of " <> (show owner)) ]
  , text " to "
  , b_
      [ text case payee of
          (Account (AccountId accNum2 owner2)) -> ("account " <> (show accNum2) <> " of " <> (show owner2))
          (Party dest) -> ("party " <> (show dest))
      ]
  , text "."
  ]

displayWarning (TransactionPartialPay (AccountId accNum owner) payee tok amount expected) =
  [ b_ [ text "TransactionPartialPay" ]
  , text " - The contract is supposed to make a payment of "
  , b_ [ text $ show expected ]
  , text " units of "
  , b_ [ text $ show tok ]
  , text " from account "
  , b_ [ text ((show accNum) <> " of " <> (show owner)) ]
  , text " to "
  , b_
      [ text case payee of
          (Account (AccountId accNum2 owner2)) -> ("account " <> (show accNum2) <> " of " <> (show owner2))
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

txInputToLines :: forall p a. Maybe TransactionInput -> Array (HTML p a)
txInputToLines Nothing = []

txInputToLines (Just (TransactionInput { interval, inputs })) = Array.fromFoldable $ map (inputToLine interval) inputs

inputToLine :: forall p a. SlotInterval -> Input -> HTML p a
inputToLine (SlotInterval start end) (IDeposit (AccountId accountNumber accountOwner) party token money) =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "Deposit "
        , strong_ [ text (show money) ]
        , text " units of "
        , strong_ [ text (show token) ]
        , text " into account "
        , strong_ [ text (show accountOwner <> " " <> show accountNumber <> "") ]
        , text " as "
        , strong_ [ text (show party) ]
        ]
    , span_ [ text $ (show start) <> " - " <> (show end) ]
    ]

inputToLine (SlotInterval start end) (IChoice (ChoiceId choiceName choiceOwner) chosenNum) =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "Participant "
        , strong_ [ text (show choiceOwner) ]
        , text " chooses the value "
        , strong_ [ text (show chosenNum) ]
        , text " for choice with id "
        , strong_ [ text (show choiceName) ]
        ]
    , span_ [ text $ (show start) <> " - " <> (show end) ]
    ]

inputToLine (SlotInterval start end) INotify =
  li [ classes [ ClassName "error-row" ] ]
    [ text "Notify"
    , span_ [ text $ (show start) <> " - " <> (show end) ]
    ]
