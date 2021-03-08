module Contract.View
  ( contractsScreen
  , contractDetailsCard
  ) where

import Prelude hiding (div)
import Contract.Types (Action(..), State)
import Css (classNames)
import Css as Css
import Data.Foldable (foldr)
import Data.Lens (view)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Halogen.HTML (HTML, a, button, div, div_, h2_, span, text)
import Halogen.HTML.Events.Extra (onClick_)
import Material.Icons as Icon
import Play.Types (ContractStatus)
import Marlowe.Execution (ExecutionStep, NamedAction(..))
import Marlowe.Semantics (Accounts, ChoiceId(..), Input(..), Party, TransactionInput(..), _accounts)

contractsScreen :: forall p. ContractStatus -> HTML p Action
contractsScreen contractStatus =
  div_
    [ h2_
        [ text "Home" ]
    , a
        [ classNames Css.fixedPrimaryButton
        , onClick_ $ ToggleTemplateLibraryCard
        ]
        [ span
            [ classNames [ "mr-0.5" ] ]
            [ text "New" ]
        , Icon.add
        ]
    ]

contractDetailsCard :: forall p. State -> HTML p Action
contractDetailsCard contractInstance =
  div_
    [ h2_
        [ text "Contract details" ]
    ]

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

renderTasks :: forall p. Map (Maybe Party) (Array Input) -> HTML p Action
renderTasks inputsMap = text ""

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
