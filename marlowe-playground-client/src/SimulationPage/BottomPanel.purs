module SimulationPage.BottomPanel where

import Control.Alternative (map)
import Data.Array (concatMap, reverse)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Either (Either(..), either)
import Data.Eq (eq, (==))
import Data.Foldable (foldMap)
import Data.HeytingAlgebra (not, (||))
import Data.Lens (_Just, has, only, previewOn, to, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.List (List, toUnfoldable)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Halogen.Classes (aHorizontal, accentBorderBottom, active, activeClass, closeDrawerArrowIcon, collapsed, first, flex, flexLeft, flexTen, footerPanelBg, minimizeIcon, rTable, rTable4cols, rTableCell, rTableDataRow, rTableEmptyRow)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), HTML, a, a_, b_, div, h2, img, li, li_, ol, section, span_, strong_, text, ul)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, class_, classes, src)
import Marlowe.Semantics (Assets(..), ChoiceId(..), Input(..), Party, Payment(..), Slot(..), SlotInterval(..), Token(..), TransactionInput(..), TransactionWarning(..), ValueId(..), _accounts, _boundValues, _choices, timeouts)
import Prelude (bind, const, mempty, pure, show, zero, ($), (<<<), (<>))
import Pretty (renderPrettyParty, renderPrettyPayee, renderPrettyToken, showPrettyMoney)
import SimulationPage.Types (Action(..), BottomPanelView(..), MarloweEvent(..), State, _SimulationNotStarted, _SimulationRunning, _bottomPanelView, _contract, _editorErrors, _editorWarnings, _executionState, _initialSlot, _log, _marloweState, _showBottomPanel, _slot, _state, _transactionError, _transactionWarnings)

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
                                [ classes ((if hasRuntimeWarnings || hasRuntimeError then [ ClassName "error-tab" ] else []) <> isActive CurrentStateView)
                                , onClick $ const $ Just $ ChangeSimulationView CurrentStateView
                                ]
                                [ a_ [ text "Current State" ] ]
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

  -- FIXME: probably remove
  warnings = state ^. (_marloweState <<< _Head <<< _editorWarnings)

  -- FIXME: probably remove
  errors = state ^. (_marloweState <<< _Head <<< _editorErrors)

  -- FIXME: check how to reach this
  hasRuntimeWarnings = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionWarnings <<< to Array.null <<< only false) state

  hasRuntimeError = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionError <<< to isJust <<< only true) state

  showingBottomPanel = state ^. _showBottomPanel

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state CurrentStateView =
  div [ class_ Classes.panelContents ]
    [ div [ classes [ rTable, rTable4cols, ClassName "panel-table" ] ]
        ( warningsRow <> errorRow
            <> eitherRow "Current Slot" (slotText)
            <> dataRow "Expiration Slot" (state ^. (_marloweState <<< _Head <<< _contract <<< to contractMaxTime))
            <> tableRow
                { title: "Accounts"
                , emptyMessage: "No accounts have been used"
                , columns: ("Participant" /\ "Token" /\ "Money")
                , rowData: accountsData
                }
            <> tableRow
                { title: "Choices"
                , emptyMessage: "No Choices have been made"
                , columns: ("Choice ID" /\ "Participant" /\ "Chosen Value")
                , rowData: choicesData
                }
            <> tableRow
                { title: "Let Bindings"
                , emptyMessage: "No values have been bound"
                , columns: ("Identifier" /\ "Value" /\ mempty)
                , rowData: bindingsData
                }
        )
    ]
  where
  contractMaxTime Nothing = "Closed"

  contractMaxTime (Just contract) =
    let
      t = (_.maxTime <<< unwrap <<< timeouts) contract
    in
      if t == zero then "Closed" else show t

  warnings = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionWarnings)

  warningsRow =
    if Array.null warnings then
      []
    else
      (headerRow "Warnings" ("type" /\ "details" /\ mempty)) <> foldMap displayWarning' warnings

  error = previewOn state (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionError <<< _Just)

  errorRow =
    if isNothing error then
      []
    else
      (headerRow "Errors" ("details" /\ mempty /\ mempty)) <> displayError error

  slotText = case previewOn state (_marloweState <<< _Head <<< _executionState <<< _SimulationNotStarted <<< _initialSlot) of
    Just initialSlot -> Right $ show initialSlot
    Nothing -> case previewOn state (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _slot) of
      Just slot -> Right $ show slot
      Nothing -> Left "Slot number not defined"

  displayError Nothing = []

  displayError (Just err) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ classes [ rTableCell, ClassName "Rtable-single-column-row" ] ] [ text $ show err ]
    ]

  accountsData =
    let
      (accounts :: Array (Tuple (Tuple Party Token) BigInteger)) = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _state <<< _accounts <<< to Map.toUnfoldable)

      asTuple (Tuple (Tuple accountOwner tok) value) = renderPrettyParty accountOwner /\ renderPrettyToken tok /\ text (showPrettyMoney value)
    in
      map asTuple accounts

  choicesData =
    let
      (choices :: Array (Tuple ChoiceId BigInteger)) = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _state <<< _choices <<< to Map.toUnfoldable)

      asTuple (Tuple (ChoiceId choiceName choiceOwner) value) = text (show choiceName) /\ renderPrettyParty choiceOwner /\ text (showPrettyMoney value)
    in
      map asTuple choices

  bindingsData =
    let
      (bindings :: Array (Tuple ValueId BigInteger)) = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _state <<< _boundValues <<< to Map.toUnfoldable)

      asTuple (Tuple (ValueId valueId) value) = text (show valueId) /\ text (showPrettyMoney value) /\ text ""
    in
      map asTuple bindings

  tableRow { title, emptyMessage, rowData: [] } = emptyRow title emptyMessage

  tableRow { title, columns, rowData } = headerRow title columns <> foldMap (\dataTuple -> row dataTuple) rowData

  headerRow title (a /\ b /\ c) =
    [ div [ classes [ rTableCell, first, Classes.header ] ] [ text title ] ]
      <> map (\x -> div [ classes [ rTableCell, rTableCell, Classes.header ] ] [ text x ]) [ a, b, c ]

  row (a /\ b /\ c) =
    [ div [ classes [ rTableCell, first ] ] [] ]
      <> map (\x -> div [ class_ rTableCell ] [ x ]) [ a, b, c ]

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

  eitherRow title = either (emptyRow title) (dataRow title)

  displayWarning' (TransactionNonPositiveDeposit party owner tok amount) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionNonPositiveDeposit" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "Party "
        , renderPrettyParty party
        , text $ " is asked to deposit "
            <> showPrettyMoney amount
            <> " units of "
        , renderPrettyToken tok
        , text " into account of "
        , renderPrettyParty owner
        , text "."
        ]
    ]

  displayWarning' (TransactionNonPositivePay owner payee tok amount) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionNonPositivePay" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        ( [ text $ "The contract is supposed to make a payment of "
              <> showPrettyMoney amount
              <> " units of "
          , renderPrettyToken tok
          , text $ " from account of "
              <> show owner
              <> " to "
          ]
            <> renderPrettyPayee payee
            <> [ text "." ]
        )
    ]

  displayWarning' (TransactionPartialPay owner payee tok amount expected) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionPartialPay" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        ( [ text $ "The contract is supposed to make a payment of "
              <> showPrettyMoney expected
              <> " units of "
          , renderPrettyToken tok
          , text " from account of "
          , renderPrettyParty owner
          , text $ " to "
          ]
            <> renderPrettyPayee payee
            <> [ text $ "."
                  <> " but there is only "
                  <> showPrettyMoney amount
                  <> "."
              ]
        )
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

panelContents state MarloweLogView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents, flexLeft ]
    ]
    content
  where
  inputLines = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _log <<< to (concatMap logToLines))

  content =
    [ div [ classes [ ClassName "error-headers", ClassName "error-row" ] ]
        [ div [] [ text "Action" ]
        , div [] [ text "Slot" ]
        ]
    , ul [] (reverse inputLines)
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
  , b_ [ renderPrettyParty party ]
  , text " deposits "
  , b_ [ text $ showPrettyMoney money ]
  , text " units of "
  , b_ [ renderPrettyToken tok ]
  , text " into account of "
  , b_ [ renderPrettyParty owner ]
  , text "."
  ]

displayInput (IChoice (ChoiceId choiceId party) chosenNum) =
  [ b_ [ text "IChoice" ]
  , text " - Party "
  , b_ [ renderPrettyParty party ]
  , text " chooses number "
  , b_ [ text $ showPrettyMoney chosenNum ]
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
  [ b_ [ text "Non-Positive Deposit" ]
  , text " - Party "
  , b_ [ renderPrettyParty party ]
  , text " is asked to deposit "
  , b_ [ text $ showPrettyMoney amount ]
  , text " units of "
  , b_ [ renderPrettyToken tok ]
  , text " into account of "
  , b_ [ renderPrettyParty owner ]
  , text "."
  ]

displayWarning (TransactionNonPositivePay owner payee tok amount) =
  [ b_ [ text "Non-Positive Pay" ]
  , text " - The contract is supposed to make a payment of "
  , b_ [ text $ showPrettyMoney amount ]
  , text " units of "
  , b_ [ renderPrettyToken tok ]
  , text " from account of "
  , b_ [ renderPrettyParty owner ]
  , text " to "
  , b_ $ renderPrettyPayee payee
  , text "."
  ]

displayWarning (TransactionPartialPay owner payee tok amount expected) =
  [ b_ [ text "Partial Pay" ]
  , text " - The contract is supposed to make a payment of "
  , b_ [ text $ showPrettyMoney expected ]
  , text " units of "
  , b_ [ renderPrettyToken tok ]
  , text " from account of "
  , b_ [ renderPrettyParty owner ]
  , text " to "
  , b_ $ renderPrettyPayee payee
  , text " but there is only "
  , b_ [ text $ showPrettyMoney amount ]
  , text "."
  ]

displayWarning (TransactionShadowing valId oldVal newVal) =
  [ b_ [ text "Value Shadowing" ]
  , text " - The contract defined the value with id "
  , b_ [ text (show valId) ]
  , text " before, it was assigned the value "
  , b_ [ text (show oldVal) ]
  , text " and now it is being assigned the value "
  , b_ [ text (show newVal) ]
  , text "."
  ]

displayWarning TransactionAssertionFailed =
  [ b_ [ text "Assertion Failed" ]
  , text " - An assertion in the contract did not hold."
  ]

logToLines :: forall p a. MarloweEvent -> Array (HTML p a)
logToLines (InputEvent (TransactionInput { interval, inputs })) = Array.fromFoldable $ map (inputToLine interval) inputs

logToLines (OutputEvent interval payment) = paymentToLines interval payment

inputToLine :: forall p a. SlotInterval -> Input -> HTML p a
inputToLine (SlotInterval start end) (IDeposit accountOwner party token money) =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "Deposit "
        , strong_ [ text (showPrettyMoney money) ]
        , text " units of "
        , strong_ [ renderPrettyToken token ]
        , text " into account of "
        , strong_ [ renderPrettyParty accountOwner ]
        , text " as "
        , strong_ [ renderPrettyParty party ]
        ]
    , span_ [ text $ (show start) <> " - " <> (show end) ]
    ]

inputToLine (SlotInterval start end) (IChoice (ChoiceId choiceName choiceOwner) chosenNum) =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "Participant "
        , strong_ [ renderPrettyParty choiceOwner ]
        , text " chooses the value "
        , strong_ [ text (showPrettyMoney chosenNum) ]
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

paymentToLines :: forall p a. SlotInterval -> Payment -> Array (HTML p a)
paymentToLines slotInterval (Payment party money) = unfoldAssets money (paymentToLine slotInterval party)

paymentToLine :: forall p a. SlotInterval -> Party -> Token -> BigInteger -> HTML p a
paymentToLine (SlotInterval start end) party token money =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "The contract pays "
        , strong_ [ text (showPrettyMoney money) ]
        , text " units of "
        , strong_ [ renderPrettyToken token ]
        , text " to participant "
        , strong_ [ renderPrettyParty party ]
        ]
    , span_ [ text $ (show start) <> " - " <> (show end) ]
    ]

unfoldAssets :: forall a. Assets -> (Token -> BigInteger -> a) -> Array a
unfoldAssets (Assets mon) f =
  concatMap
    ( \(Tuple currencySymbol tokenMap) ->
        ( map
            ( \(Tuple tokenName value) ->
                f (Token currencySymbol tokenName) value
            )
            (Map.toUnfoldable tokenMap)
        )
    )
    (Map.toUnfoldable mon)
