module Contract.View
  ( contractDetailsCard
  ) where

import Prelude hiding (div)
import Contract.Lenses (_executionState, _metadata, _step, _tab)
import Contract.Types (Action(..), State, Tab(..))
import Css (classNames)
import Data.BigInteger (fromInt)
import Data.Foldable (foldr)
import Data.Lens (view, (^.))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Halogen.HTML (HTML, a, button, div, h1, h2, span, span_, text)
import Halogen.HTML.Events.Extra (onClick_)
import Marlowe.Execution (ExecutionStep, NamedAction(..), _namedActions)
import Marlowe.Extended (contractTypeName)
import Marlowe.Semantics (Accounts, ChoiceId(..), Input(..), Party(..), Token(..), TransactionInput(..), _accounts)

contractDetailsCard :: forall p. State -> HTML p Action
contractDetailsCard state =
  let
    metadata = state ^. _metadata
  in
    div [ classNames [ "flex", "flex-col", "items-center" ] ]
      [ h1 [ classNames [ "text-xl", "font-medium" ] ] [ text metadata.contractName ]
      , h2 [ classNames [ "mb-0.5" ] ] [ text $ contractTypeName metadata.contractType ]
      -- FIXME: Revisit width (at least on desktop)
      , div [ classNames [ "w-full" ] ] [ renderCurrentState state ]
      ]

renderCurrentState :: forall p. State -> HTML p Action
renderCurrentState state =
  let
    -- As programmers we use 0-indexed arrays and steps, but we number steps
    -- starting from 1
    stepNumber = state ^. _step + 1

    executionState = state ^. _executionState

    currentTab = state ^. _tab

    tabSelector isActive =
      [ "flex-grow", "text-center", "font-semibold", "py-0.5", "trapesodial-card-selector" ]
        <> case isActive of
            true -> [ "active" ]
            false -> []
  in
    div [ classNames [ "rounded-xl", "overflow-hidden" ] ]
      [ div [ classNames [ "flex", "overflow-hidden" ] ]
          [ a
              [ classNames (tabSelector $ currentTab == Tasks)
              , onClick_ $ SelectTab Tasks
              ]
              [ span_ $ [ text "Tasks" ] ]
          , a
              [ classNames (tabSelector $ currentTab == Balances)
              , onClick_ $ SelectTab Balances
              ]
              [ span_ $ [ text "Balances" ] ]
          ]
      , div [ classNames [ "px-1", "py-0.5", "bg-white" ] ]
          [ span [] [ text $ "Step " <> show stepNumber ]
          , span [] [ text "Completed" ]
          ]
      , div [ classNames [ "px-1", "py-0.5", "bg-white" ] ]
          [ renderTasks (executionState ^. _namedActions)
          ]
      ]

renderTasks :: forall p. Array NamedAction -> HTML p Action
renderTasks actions =
  let
    -- FIXME: We fake the namedActions for development until we fix the semantics
    actions' =
      [ MakeDeposit (Role "into account") (Role "by") (Token "" "") $ fromInt 1500
      ]
  in
    -- FIXME: need to group by role
    div [] $ actions' <#> renderAction

renderAction :: forall p. NamedAction -> HTML p Action
renderAction (MakeDeposit intoAccountOf by token value) = text "make deposit"

renderAction (MakeChoice _ _ _) = text "make choice"

renderAction (MakeNotify _) = text "awaiting observation?"

renderAction (Evaluate _) = text "FIXME: what should we put here? Evaluate"

renderAction CloseContract = text "FIXME: what should we put here? CloseContract"

getParty :: Input -> Maybe Party
getParty (IDeposit _ p _ _) = Just p

getParty (IChoice (ChoiceId _ p) _) = Just p

getParty _ = Nothing

renderPastStep :: forall p. ExecutionStep -> HTML p Action
renderPastStep { state, timedOut: true } =
  let
    balances = renderBalances (view _accounts state)
  in
    text ""

renderPastStep { txInput: TransactionInput { inputs }, state } =
  let
    balances = renderBalances (view _accounts state)

    f :: Input -> Map (Maybe Party) (Array Input) -> Map (Maybe Party) (Array Input)
    f input acc = Map.insertWith append (getParty input) [ input ] acc

    inputsMap = foldr f mempty inputs

    tasks = renderCompletedTasks inputsMap
  in
    text ""

renderCompletedTasks :: forall p. Map (Maybe Party) (Array Input) -> HTML p Action
renderCompletedTasks inputsMap = text ""

renderBalances :: forall p. Accounts -> HTML p Action
renderBalances accounts = text ""

renderNamedAction :: forall p. NamedAction -> HTML p Action
renderNamedAction (MakeDeposit accountId party token amount) =
  let
    input = IDeposit accountId party token amount
  in
    button [ onClick_ $ ChooseInput (Just input) ]
      [ div [] [ text "deposit", text "some ada" ] ]

renderNamedAction (MakeChoice choiceId bounds chosenNum) =
  let
    input = IChoice choiceId chosenNum
  in
    button [ onClick_ $ ChooseInput (Just input) ]
      [ div [] [ text "deposit", text "some ada" ] ]

renderNamedAction (MakeNotify observation) =
  let
    input = INotify
  in
    button [ onClick_ $ ChooseInput (Just input) ]
      [ div [] [ text "deposit", text "some ada" ] ]

renderNamedAction (Evaluate { payments, bindings }) =
  button [ onClick_ $ ChooseInput Nothing ]
    [ div [] [ text "deposit", text "some ada" ] ]

renderNamedAction CloseContract =
  button [ onClick_ $ ChooseInput Nothing ]
    [ div [] [ text "deposit", text "some ada" ] ]
