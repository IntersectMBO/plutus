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
import Data.Set as Set
import Halogen.HTML (HTML, a, button, div, h1, h2, span, span_, text)
import Halogen.HTML.Events.Extra (onClick_)
import Marlowe.Execution (ExecutionStep, NamedAction(..), _contract, _namedActions)
import Marlowe.Extended (contractTypeName)
import Marlowe.HasParties (getParties)
import Marlowe.Semantics (Accounts, ChoiceId(..), Input(..), Party(..), Token(..), TransactionInput(..), _accounts)
import Material.Icons as Icons
import WalletData.Types (WalletDetails)

contractDetailsCard :: forall p. WalletDetails -> State -> HTML p Action
contractDetailsCard walletDetails state =
  let
    metadata = state ^. _metadata
  in
    div [ classNames [ "flex", "flex-col", "items-center" ] ]
      [ h1 [ classNames [ "text-xl", "font-semibold" ] ] [ text metadata.contractName ]
      -- FIXME: in zeplin the contractType is defined with color #283346, we need to define
      --        the color palette with russ.
      , h2 [ classNames [ "mb-2", "text-xs", "uppercase" ] ] [ text $ contractTypeName metadata.contractType ]
      -- FIXME: Revisit width (at least on desktop)
      , div [ classNames [ "w-full" ] ] [ renderCurrentState walletDetails state ]
      ]

renderCurrentState :: forall p. WalletDetails -> State -> HTML p Action
renderCurrentState walletDetails state =
  let
    -- As programmers we use 0-indexed arrays and steps, but we number steps
    -- starting from 1
    stepNumber = state ^. _step + 1

    currentTab = state ^. _tab

    -- FIXME: in zepplin the font size is 6px (I think the scale is wrong), but proportionally is half of
    --        of the size of the Contract Title. I've set it a little bit bigger as it looked weird. Check with
    --        russ.
    tabSelector isActive =
      [ "flex-grow", "text-center", "py-2", "trapesodial-card-selector", "text-sm", "font-semibold" ]
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
      , div [ classNames [ "px-4", "bg-white" ] ]
          -- FIXME: zeplin has border color #dfdfdf, see if it makes sense to add that one to the pallete
          --        or if this gray is fine
          [ div [ classNames [ "py-2.5", "flex", "items-center", "border-b", "border-gray" ] ]
              [ span
                  [ classNames [ "text-xl", "font-semibold", "flex-grow" ] ]
                  [ text $ "Step " <> show stepNumber ]
              , span
                  -- [ "flex", "items-center", "justify-center", "px-4", "py-3", "leading-none", "disabled:opacity-50", "disabled:cursor-not-allowed",  ]
                  [ classNames [ "flex-grow", "rounded-3xl", "bg-gray", "py-2", "flex", "items-center" ] ]
                  [ Icons.timer' [ "pl-3" ]
                  , span [ classNames [ "text-xs", "flex-grow", "text-center", "font-semibold" ] ]
                      [ text "1hr 2mins left" ]
                  ]
              ]
          , div [ classNames [ "py-2" ] ]
              [ renderTasks walletDetails state
              ]
          ]
      ]

renderTasks :: forall p. WalletDetails -> State -> HTML p Action
renderTasks walletDetails state =
  let
    executionState = state ^. _executionState

    actions = executionState ^. _namedActions

    contract = executionState ^. _contract

    getRoleEntry = case _ of
      (PK _) -> Nothing
      (Role roleName) -> Just roleName

    roles :: Array String
    roles = Set.toUnfoldable $ Set.mapMaybe getRoleEntry (getParties contract)

    -- FIXME: We fake the namedActions for development until we fix the semantics
    actions' =
      [ MakeDeposit (Role "into account") (Role "by") (Token "" "") $ fromInt 1500
      ]
  in
    -- FIXME: need to group by role
    div []
      [ span_ [ text $ "Role (" <> walletDetails.nickname <> ")" ]
      , div [] $ actions' <#> renderAction
      ]

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
