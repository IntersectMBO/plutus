module SimulationPage.BottomPanel (bottomPanel) where

import Prelude hiding (div)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Either (Either(..))
import Data.Foldable (foldMap)
import Data.Lens (has, only, previewOn, to, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Halogen.Classes (aHorizontal, accentBorderBottom, active, activeClass, closeDrawerArrowIcon, collapsed, first, flex, flexTen, footerPanelBg, minimizeIcon, rTable, rTable4cols, rTableCell, rTableEmptyRow)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), HTML, a, a_, div, img, li, section, text, ul)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, class_, classes, src)
import Marlowe.Semantics (ChoiceId(..), Party, Token, ValueId(..), _accounts, _boundValues, _choices)
import Pretty (renderPrettyParty, renderPrettyToken, showPrettyMoney)
import SimulationPage.Types (Action(..), BottomPanelView(..), State, _SimulationNotStarted, _SimulationRunning, _bottomPanelView, _executionState, _initialSlot, _marloweState, _showBottomPanel, _slot, _state, _transactionError, _transactionWarnings)

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

  -- QUESTION: what are runtimeWarnings and runtimeError? how can I reach that state?
  hasRuntimeWarnings = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionWarnings <<< to Array.null <<< only false) state

  hasRuntimeError = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionError <<< to isJust <<< only true) state

  showingBottomPanel = state ^. _showBottomPanel

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state CurrentStateView =
  div [ class_ Classes.panelContents ]
    [ div [ classes [ rTable, rTable4cols, ClassName "panel-table" ] ]
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
    ]
  where
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
