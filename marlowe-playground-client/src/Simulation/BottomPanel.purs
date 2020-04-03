module Simulation.BottomPanel where

import Control.Alternative (map)
import Data.Array (concatMap, drop, head, length, tail)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Eq (eq, (==))
import Data.Foldable (foldMap)
import Data.HeytingAlgebra (not, (||))
import Data.Lens (to, view, (^.))
import Data.List (List, toUnfoldable)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, isNothing)
import Data.String (take)
import Data.String.Extra (unlines)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Halogen.Classes (aHorizontal, accentBorderBottom, closeDrawerIcon, first, flex, flexLeft, flexTen, footerPanelBg, isActiveTab, minimizeIcon, rTable, rTable6cols, rTableCell, rTableEmptyRow, simulationBottomPanel, spanText)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), HTML, a, a_, b_, button, code_, div, h2, h3_, img, li, li_, ol, ol_, pre, section, span_, text, ul, ul_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, class_, classes, enabled, src)
import Marlowe.Parser (transactionInputList, transactionWarningList)
import Marlowe.Semantics (AccountId(..), Assets(..), ChoiceId(..), Input(..), Payee(..), Payment(..), Slot(..), SlotInterval(..), Token(..), TransactionInput(..), TransactionWarning(..), ValueId(..), _accounts, _boundValues, _choices, maxTime)
import Marlowe.Symbolic.Types.Response as R
import Network.RemoteData (RemoteData(..), isLoading)
import Prelude (bind, const, mempty, pure, show, zero, ($), (<<<), (<>), (/=), (&&), (<$>))
import Text.Parsing.StringParser (runParser)
import Text.Parsing.StringParser.Basic (lines)
import Types (FrontendState, HAction(..), SimulationBottomPanelView(MarloweErrorsView, MarloweWarningsView, StaticAnalysisView, CurrentStateView), View(Simulation), _Head, _analysisState, _contract, _editorErrors, _editorWarnings, _marloweState, _payments, _showBottomPanel, _showErrorDetail, _simulationBottomPanelView, _slot, _state, _transactionError, _transactionWarnings)

isContractValid :: FrontendState -> Boolean
isContractValid state =
  (view (_marloweState <<< _Head <<< _contract) state /= Nothing)
    && (view (_marloweState <<< _Head <<< _editorErrors <<< to Array.null) state)

bottomPanel :: forall p. FrontendState -> HTML p HAction
bottomPanel state =
  div [ classes (simulationBottomPanel state) ]
    [ div [ class_ flex ]
        [ div [ class_ flexTen ]
            [ div [ classes (footerPanelBg state Simulation <> isActiveTab state Simulation) ]
                [ section [ classes [ ClassName "panel-header", aHorizontal ] ]
                    [ div [ classes ([ ClassName "panel-sub-header-main", aHorizontal ] <> (if state ^. _showBottomPanel then [ accentBorderBottom ] else [])) ]
                        [ ul [ classes [ ClassName "demo-list", aHorizontal ] ]
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
                            ]
                        , ul [ classes [ ClassName "end-item", aHorizontal ] ]
                            [ li [ classes [ Classes.stateLabel ] ]
                                [ text "Contract Expiration: ", state ^. (_marloweState <<< _Head <<< _contract <<< to contractMaxTime <<< to text) ]
                            , li [ classes [ ClassName "space-left", Classes.stateLabel ] ]
                                [ text "Current Blocks: ", state ^. (_marloweState <<< _Head <<< _slot <<< to show <<< to text) ]
                            , li [ class_ (ClassName "space-left") ]
                                [ a [ onClick $ const $ Just $ ShowBottomPanel (state ^. _showBottomPanel <<< to not) ]
                                    [ img [ classes (minimizeIcon state), src closeDrawerIcon, alt "close drawer icon" ] ]
                                ]
                            ]
                        ]
                    ]
                , panelContents state (state ^. _simulationBottomPanelView)
                ]
            ]
        ]
    ]
  where
  isActive view = if state ^. _simulationBottomPanelView <<< (to (eq view)) then [ ClassName "active-text" ] else []

  warnings = state ^. (_marloweState <<< _Head <<< _editorWarnings)

  errors = state ^. (_marloweState <<< _Head <<< _editorErrors)

  hasRuntimeWarnings = state ^. (_marloweState <<< _Head <<< _transactionWarnings <<< to Array.null <<< to not)

  hasRuntimeError = state ^. (_marloweState <<< _Head <<< _transactionError <<< to isJust)

  contractMaxTime Nothing = "Closed"

  contractMaxTime (Just contract) = let t = maxTime contract in if t == zero then "Closed" else show t

panelContents :: forall p. FrontendState -> SimulationBottomPanelView -> HTML p HAction
panelContents state CurrentStateView =
  div [ class_ Classes.panelContents ]
    [ div [ classes [ rTable, rTable6cols, ClassName "panel-table" ] ]
        ( warningsRow <> errorRow
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

panelContents state StaticAnalysisView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents ]
    ]
    [ analysisResultPane state
    , button [ onClick $ const $ Just $ AnalyseContract, enabled enabled', classes (if enabled' then [] else [ ClassName "disabled" ]) ]
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
    li [ classes [ ClassName "warning-content", ClassName "error-row" ] ]
      [ text warning.message
      , a [ onClick $ const $ Just $ MarloweMoveToPosition warning.startLineNumber warning.startColumn ]
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
    li [ classes [ ClassName "error-content", ClassName "error-row", ClassName "flex-wrap" ] ]
      ( [ a [ onClick $ const $ Just $ ShowErrorDetail (state ^. (_showErrorDetail <<< to not)) ]
            [ text error.firstLine ]
        , a [ onClick $ const $ Just $ MarloweMoveToPosition error.startLineNumber error.startColumn ]
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

analysisResultPane :: forall p. FrontendState -> HTML p HAction
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
          [ h3_ [ text "Analysis Result: Pass" ]
          , text "Static analysis could not find any execution that results in any warning."
          ]
      Success (R.CounterExample { initialSlot, transactionList, transactionWarning }) ->
        explanation
          [ h3_ [ text "Analysis Result: Warnings Found" ]
          , text "Static analysis found the following counterexample:"
          , ul_
              [ li_
                  [ spanText "Initial slot: "
                  , b_ [ spanText (show initialSlot) ]
                  ]
              , li_
                  [ spanText "Offending transaction list: "
                  , displayTransactionList transactionList
                  ]
              , li_
                  [ spanText "Warnings issued: "
                  , displayWarningList transactionWarning
                  ]
              ]
          ]
      Success (R.Error str) ->
        explanation
          [ h3_ [ text "Error during analysis" ]
          , text "Analysis failed for the following reason:"
          , ul_
              [ li_
                  [ b_ [ spanText str ]
                  ]
              ]
          ]
      Failure failure ->
        explanation
          [ h3_ [ text "Error during analysis" ]
          , text "Analysis failed for the following reason:"
          , ul_
              [ li_
                  [ b_ [ spanText failure ]
                  ]
              ]
          ]
      Loading -> text ""

displayTransactionList :: forall p. String -> HTML p HAction
displayTransactionList transactionList = case runParser transactionInputList transactionList of
  Right pTL ->
    ol_
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

displayInputList :: forall p. List Input -> HTML p HAction
displayInputList inputList =
  ol_
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

displayWarningList :: forall p. String -> HTML p HAction
displayWarningList transactionWarnings = case runParser transactionWarningList transactionWarnings of
  Right pWL ->
    ol_
      ( do
          warning <- ((toUnfoldable pWL) :: Array TransactionWarning)
          pure (li_ (displayWarning warning))
      )
  Left _ -> code_ [ text transactionWarnings ]

displayWarnings :: forall p. Array TransactionWarning -> HTML p HAction
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

displayWarning :: forall p. TransactionWarning -> Array (HTML p HAction)
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
