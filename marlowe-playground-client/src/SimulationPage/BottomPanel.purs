module SimulationPage.BottomPanel (panelContents) where

import Prelude hiding (div)
import Data.BigInteger (BigInteger)
import Data.Either (Either(..))
import Data.Foldable (foldMap)
import Data.Lens (preview, previewOn, to, view, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Classes (first, rTable, rTable4cols, rTableCell, rTableEmptyRow)
import Halogen.Classes as Classes
import Halogen.Css (classNames)
import Halogen.HTML (HTML, br_, div, div_, h4, text)
import Halogen.HTML.Properties (class_, classes)
import MainFrame.Types (ChildSlots)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Semantics (ChoiceId(..), Party, Token, TransactionError, TransactionWarning, ValueId(..), _accounts, _boundValues, _choices)
import Marlowe.ViewPartials (displayWarningList)
import Pretty (renderPrettyParty, renderPrettyToken, showPrettyMoney)
import SimulationPage.Types (BottomPanelView(..), State)
import Simulator.Lenses (_SimulationNotStarted, _SimulationRunning, _executionState, _initialSlot, _marloweState, _slot, _state, _transactionError, _transactionWarnings)

panelContents ::
  forall m action.
  MonadAff m =>
  MetaData ->
  State ->
  BottomPanelView ->
  ComponentHTML action ChildSlots m
panelContents metadata state CurrentStateView = currentStateView metadata state

panelContents metadata state WarningsAndErrorsView =
  let
    runtimeWarnings = view (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionWarnings) state

    mRuntimeError = join $ preview (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionError) state
  in
    warningsAndErrorsView runtimeWarnings mRuntimeError

currentStateView :: forall p action. MetaData -> State -> HTML p action
currentStateView metadata state =
  div [ classes [ rTable, rTable4cols ] ]
    ( tableRow
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
  where
  slotText = case previewOn state (_marloweState <<< _Head <<< _executionState <<< _SimulationNotStarted <<< _initialSlot) of
    Just initialSlot -> Right $ show initialSlot
    Nothing -> case previewOn state (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _slot) of
      Just slot -> Right $ show slot
      Nothing -> Left "Slot number not defined"

  accountsData =
    let
      (accounts :: Array (Tuple (Tuple Party Token) BigInteger)) = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _state <<< _accounts <<< to Map.toUnfoldable)

      asTuple (Tuple (Tuple accountOwner tok) value) = renderPrettyParty metadata accountOwner /\ renderPrettyToken tok /\ text (showPrettyMoney value)
    in
      map asTuple accounts

  choicesData =
    let
      (choices :: Array (Tuple ChoiceId BigInteger)) = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _state <<< _choices <<< to Map.toUnfoldable)

      asTuple (Tuple (ChoiceId choiceName choiceOwner) value) = text (show choiceName) /\ renderPrettyParty metadata choiceOwner /\ text (showPrettyMoney value)
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

warningsAndErrorsView ::
  forall action m.
  MonadAff m =>
  Array TransactionWarning ->
  Maybe TransactionError ->
  ComponentHTML action ChildSlots m
warningsAndErrorsView [] Nothing = div_ [ text "No problems found" ]

warningsAndErrorsView [] (Just err) = errorView err

warningsAndErrorsView warnings Nothing = warningsView warnings

warningsAndErrorsView warnings (Just err) =
  div_
    [ errorView err
    , br_
    , warningsView warnings
    ]

warningsView ::
  forall action m.
  MonadAff m =>
  Array TransactionWarning ->
  ComponentHTML action ChildSlots m
warningsView warnings =
  div_
    [ h4 [ classNames [ "font-semibold", "no-margins", "mb-2" ] ] [ text "Warnings" ]
    , displayWarningList warnings
    ]

errorView ::
  forall action m.
  MonadAff m =>
  TransactionError ->
  ComponentHTML action ChildSlots m
errorView err =
  div_
    [ h4 [ classNames [ "font-semibold", "no-margins", "mb-2" ] ] [ text "Error" ]
    -- TODO: Improve the error messages
    , text $ show err
    ]
