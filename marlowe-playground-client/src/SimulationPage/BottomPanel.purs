module SimulationPage.BottomPanel (bottomPanel) where

import Control.Alternative (map)
import Data.Array (concatMap, reverse)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Either (Either(..), either)
import Data.Eq (eq, (==))
import Data.Foldable (foldMap)
import Data.HeytingAlgebra (not, (||))
import Data.Lens (has, only, previewOn, to, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Halogen.Classes (aHorizontal, accentBorderBottom, active, activeClass, closeDrawerArrowIcon, collapsed, first, flex, flexLeft, flexTen, footerPanelBg, minimizeIcon, rTable, rTable4cols, rTableCell, rTableDataRow, rTableEmptyRow)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), HTML, a, a_, div, img, li, section, span_, strong_, text, ul)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, class_, classes, src)
import Marlowe.Semantics (Assets(..), ChoiceId(..), Input(..), Party, Payment(..), SlotInterval(..), Token(..), TransactionInput(..), ValueId(..), _accounts, _boundValues, _choices, timeouts)
import Prelude (const, mempty, show, zero, ($), (<<<), (<>))
import Pretty (renderPrettyParty, renderPrettyToken, showPrettyMoney)
import SimulationPage.Types (Action(..), BottomPanelView(..), MarloweEvent(..), State, _SimulationNotStarted, _SimulationRunning, _bottomPanelView, _contract, _executionState, _initialSlot, _log, _marloweState, _showBottomPanel, _slot, _state, _transactionError, _transactionWarnings)

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

  -- FIXME: check how to reach this
  hasRuntimeWarnings = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionWarnings <<< to Array.null <<< only false) state

  hasRuntimeError = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionError <<< to isJust <<< only true) state

  showingBottomPanel = state ^. _showBottomPanel

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state CurrentStateView =
  div [ class_ Classes.panelContents ]
    [ div [ classes [ rTable, rTable4cols, ClassName "panel-table" ] ]
        ( eitherRow "Current Slot" (slotText)
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

  slotText = case previewOn state (_marloweState <<< _Head <<< _executionState <<< _SimulationNotStarted <<< _initialSlot) of
    Just initialSlot -> Right $ show initialSlot
    Nothing -> case previewOn state (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _slot) of
      Just slot -> Right $ show slot
      Nothing -> Left "Slot number not defined"

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
