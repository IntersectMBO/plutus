module Contract.View
  ( contractDetailsCard
  , actionConfirmationCard
  ) where

import Prelude hiding (div)
import Contract.Lenses (_executionState, _mActiveUserParty, _metadata, _participants, _step, _tab)
import Contract.Types (Action(..), State, Tab(..))
import Css (applyWhen, classNames)
import Css as Css
import Data.Array (intercalate)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.BigInteger (BigInteger, fromInt, fromString, toNumber)
import Data.Foldable (foldMap)
import Data.Formatter.Number (Formatter(..), format)
import Data.Lens ((^.))
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe, maybe')
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.String.Extra (capitalize)
import Data.Tuple (Tuple(..), fst, uncurry)
import Data.Tuple.Nested ((/\))
import Halogen.HTML (HTML, a, button, div, div_, h1, h2, h3, input, p, span, span_, sup_, text)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), enabled, href, placeholder, target, type_, value)
import Marlowe.Execution (NamedAction(..), _contract, _namedActions, _state, getActionParticipant)
import Marlowe.Extended (contractTypeName)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Input(..), Party(..), Token(..), _accounts, getEncompassBound)
import Material.Icons (Icon(..), icon)

contractDetailsCard :: forall p. State -> HTML p Action
contractDetailsCard state =
  let
    metadata = state ^. _metadata
  in
    div [ classNames [ "flex", "flex-col", "items-center", "my-5" ] ]
      [ h1 [ classNames [ "text-xl", "font-semibold" ] ] [ text metadata.contractName ]
      -- FIXME: in zeplin the contractType is defined with color #283346, we need to define
      --        the color palette with russ.
      , h2 [ classNames [ "mb-2", "text-xs", "uppercase" ] ] [ text $ contractTypeName metadata.contractType ]
      , div [ classNames [ "w-full", "px-5", "max-w-contract-card" ] ] [ renderCurrentStep state ]
      ]

actionConfirmationCard :: forall p. State -> NamedAction -> HTML p Action
actionConfirmationCard state namedAction =
  let
    -- As programmers we use 0-indexed arrays and steps, but we number steps
    -- starting from 1
    stepNumber = state ^. _step + 1

    title = case namedAction of
      MakeDeposit _ _ _ _ -> "Deposit confirmation"
      MakeChoice _ _ _ -> "Choice confirmation"
      CloseContract -> "Close contract"
      _ -> "Fixme, this should not happen"

    cta = case namedAction of
      MakeDeposit _ _ _ _ -> "Deposit"
      MakeChoice _ _ _ -> "Choose"
      CloseContract -> "Pay to close"
      _ -> "Fixme, this should not happen"

    detailItem titleHtml amountHtml hasLeftItem =
      div [ classNames ([ "flex", "flex-col", "flex-1", "mb-2" ] <> applyWhen hasLeftItem [ "pl-2", "border-l", "border-gray" ]) ]
        [ span [ classNames [ "text-xs" ] ] titleHtml
        , span [ classNames [ "font-semibold" ] ] amountHtml
        ]

    transactionFeeItem = detailItem [ text "Transaction fee", sup_ [ text "*" ], text ":" ] [ text "₳ 0.00" ]

    actionAmountItems = case namedAction of
      MakeDeposit _ _ token amount ->
        [ detailItem [ text "Deposit amount:" ] [ currency token amount ] false
        , transactionFeeItem true
        ]
      MakeChoice _ _ (Just option) ->
        [ detailItem [ text "You are choosing:" ] [ text $ "[ option " <> show option <> " ]" ] false
        , transactionFeeItem true
        ]
      _ -> [ transactionFeeItem false ]

    totalToPay = case namedAction of
      MakeDeposit _ _ token amount -> currency token amount
      _ -> currency (Token "" "") (fromInt 0)
  in
    div_
      [ div [ classNames [ "flex", "font-semibold", "justify-between", "bg-lightgray", "p-5" ] ]
          [ span_ [ text "Demo wallet balance:" ]
          -- FIXME: remove placeholder with actual value
          , span_ [ text "$223,456.78" ]
          ]
      , div [ classNames [ "px-5", "pb-6", "pt-3", "md:pb-8" ] ]
          [ h2
              [ classNames [ "text-xl", "font-semibold" ] ]
              [ text $ "Step " <> show stepNumber ]
          , h3
              [ classNames [ "text-xs", "font-semibold" ] ]
              [ text title ]
          , div [ classNames [ "flex", "border-b", "border-gray", "mt-4" ] ]
              actionAmountItems
          , h3
              [ classNames [ "mt-4", "text-sm", "font-semibold" ] ]
              [ text "Confirm payment of:" ]
          , div
              [ classNames [ "mb-4", "text-blue", "font-semibold", "text-2xl" ] ]
              [ totalToPay ]
          , div [ classNames [ "flex", "justify-center" ] ]
              [ button
                  [ classNames $ Css.secondaryButton <> [ "mr-2", "flex-1" ]
                  , onClick_ CancelConfirmation
                  ]
                  [ text "Cancel" ]
              , button
                  [ classNames $ Css.primaryButton <> [ "flex-1" ]
                  -- FIXME: Create an action that comunicates with the backend
                  -- , onClick_ $ AskWalletConfirmation namedAction
                  ]
                  [ text cta ]
              ]
          , div [ classNames [ "bg-black", "text-white", "p-4", "mt-4", "rounded" ] ]
              [ h3 [ classNames [ "text-sm", "font-semibold" ] ] [ sup_ [ text "*" ], text "Transaction fees are estimates only:" ]
              , p [ classNames [ "pb-4", "border-b-half", "border-lightgray", "text-xs", "text-gray" ] ]
                  -- FIXME: review text with simon
                  [ text "In the demo all fees are free but in the live version the cost will depend on the status of the blockchain at the moment of the transaction" ]
              , div [ classNames [ "pt-4", "flex", "justify-between", "items-center" ] ]
                  [ a
                      -- FIXME: where should this link point to?
                      [ href "https://docs.cardano.org/en/latest/explore-cardano/cardano-fee-structure.html"
                      , classNames [ "font-bold" ]
                      , target "_blank"
                      ]
                      [ text "Read more in Docs" ]
                  , icon ArrowRight [ "text-2xl" ]
                  ]
              ]
          ]
      ]

renderCurrentStep :: forall p. State -> HTML p Action
renderCurrentStep state =
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
    div [ classNames [ "rounded", "shadow-current-step", "overflow-hidden" ] ]
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
      , div [ classNames [ "max-h-contract-card", "bg-white" ] ]
          [ div [ classNames [ "py-2.5", "px-4", "flex", "items-center", "border-b", "border-lightgray" ] ]
              [ span
                  [ classNames [ "text-xl", "font-semibold", "flex-grow" ] ]
                  [ text $ "Step " <> show stepNumber ]
              , span
                  [ classNames [ "flex-grow", "rounded-lg", "bg-lightgray", "py-2", "flex", "items-center" ] ]
                  [ icon Timer [ "pl-3" ]
                  , span [ classNames [ "text-xs", "flex-grow", "text-center", "font-semibold" ] ]
                      [ text "1hr 2mins left" ]
                  ]
              ]
          , div [ classNames [ "h-contract-card", "overflow-y-scroll", "px-4" ] ]
              [ if currentTab == Tasks then
                  renderTasks state
                else
                  renderBalances state
              ]
          ]
      ]

-- This helper function expands actions that can be taken by anybody,
-- then groups by participant and sorts it so that the owner starts first and the rest go
-- in alphabetical order
expandAndGroupByRole ::
  Maybe Party ->
  Set Party ->
  Array NamedAction ->
  Array (Tuple Party (Array NamedAction))
expandAndGroupByRole mActiveUserParty allParticipants actions =
  expandedActions
    # Array.sortBy currentPartyFirst
    # Array.groupBy sameParty
    # map extractGroupedParty
  where
  -- If an action has a participant, just use that, if it doesn't expand it to all
  -- participants
  expandedActions :: Array (Tuple Party NamedAction)
  expandedActions =
    actions
      # foldMap \action -> case getActionParticipant action of
          Just participant -> [ participant /\ action ]
          Nothing -> Set.toUnfoldable allParticipants <#> \participant -> participant /\ action

  currentPartyFirst (Tuple party1 _) (Tuple party2 _)
    | Just party1 == mActiveUserParty = LT
    | Just party2 == mActiveUserParty = GT
    | otherwise = compare party1 party2

  sameParty a b = fst a == fst b

  extractGroupedParty :: NonEmptyArray (Tuple Party NamedAction) -> Tuple Party (Array NamedAction)
  extractGroupedParty group = case NEA.unzip group of
    tokens /\ actions' -> NEA.head tokens /\ NEA.toArray actions'

renderTasks :: forall p. State -> HTML p Action
renderTasks state =
  let
    executionState = state ^. _executionState

    actions = executionState ^. _namedActions

    expandedActions =
      expandAndGroupByRole
        (state ^. _mActiveUserParty)
        (Map.keys $ state ^. _participants)
        actions

    contract = executionState ^. _contract
  in
    div [ classNames [ "pb-4" ] ] $ expandedActions <#> uncurry (renderPartyTasks state)

participantWithNickname :: State -> Party -> String
participantWithNickname state party =
  let
    mNickname :: Maybe String
    mNickname = join $ Map.lookup party (state ^. _participants)
  in
    capitalize case party /\ mNickname of
      -- TODO: For the demo we wont have PK, but eventually we probably want to limit the amount of characters
      PK publicKey /\ _ -> publicKey
      Role roleName /\ Just nickname -> roleName <> " (" <> nickname <> ")"
      Role roleName /\ Nothing -> roleName

renderPartyTasks :: forall p. State -> Party -> Array NamedAction -> HTML p Action
renderPartyTasks state party actions =
  let
    isActiveParticipant = (state ^. _mActiveUserParty) == Just party

    actionsSeparatedByOr =
      intercalate
        [ div [ classNames [ "font-semibold", "text-center", "my-2", "text-xs" ] ] [ text "OR" ]
        ]
        (Array.singleton <<< renderAction state isActiveParticipant <$> actions)

    participantName = participantWithNickname state party
  in
    div [ classNames [ "mt-3" ] ]
      ( [ div [ classNames [ "text-xs", "flex", "mb-2" ] ]
            -- TODO: In zeplin all participants have a different color. We need to decide how are we going to assing
            --       colors to users. For now they all have blue
            [ div [ classNames [ "bg-gradient-to-r", "from-blue", "to-lightblue", "text-white", "rounded-full", "w-5", "h-5", "text-center", "mr-1" ] ] [ text $ String.take 1 participantName ]
            , div [ classNames [ "font-semibold" ] ] [ text participantName ]
            ]
        ]
          <> actionsSeparatedByOr
      )

renderAction :: forall p. State -> Boolean -> NamedAction -> HTML p Action
renderAction _ isActiveParticipant namedAction@(MakeDeposit intoAccountOf by token value) =
  div_
    [ shortDescription isActiveParticipant "chocolate pastry apple pie lemon drops apple pie halvah FIXME"
    , button
        -- FIXME: adapt to use button classes from Css module
        [ classNames $ [ "flex", "justify-between", "px-6", "font-bold", "w-full", "py-4", "mt-2", "rounded-lg", "shadow" ]
            <> if isActiveParticipant then
                [ "bg-gradient-to-r", "from-blue", "to-lightblue", "text-white" ]
              else
                [ "bg-gray", "text-black", "opacity-50", "cursor-default" ]
        , enabled isActiveParticipant
        , onClick_ $ AskConfirmation namedAction
        ]
        [ span_ [ text "Deposit:" ]
        , span_ [ currency token value ]
        ]
    ]

renderAction state isActiveParticipant namedAction@(MakeChoice choiceId bounds mChosenNum) =
  let
    -- NOTE': We could eventually add an heuristic that if the difference between min and max is less
    --        than 10 elements, we could show a `select` instead of a input[number] and if the min==max
    --        we use a button that says "Choose `min`"
    Bound minBound maxBound = getEncompassBound bounds

    isValid = maybe false (between minBound maxBound) mChosenNum
  in
    div_
      [ shortDescription isActiveParticipant "chocolate pastry apple pie lemon drops apple pie halvah FIXME"
      , div
          [ classNames [ "flex", "w-full", "shadow", "rounded-lg", "mt-2", "overflow-hidden", "focus-within:ring-1", "ring-black" ]
          ]
          [ input
              [ classNames [ "border-0", "py-4", "pl-4", "pr-1", "flex-grow", "focus:ring-0" ]
              , type_ InputNumber
              , maybe'
                  (\_ -> placeholder $ "Choose between " <> show minBound <> " and " <> show maxBound)
                  (value <<< show)
                  mChosenNum
              , onValueInput_ $ ChangeChoice choiceId <<< fromString
              ]
          , button
              [ classNames
                  ( [ "px-5", "font-bold" ]
                      <> if isValid then
                          [ "bg-gradient-to-b", "from-blue", "to-lightblue", "text-white" ]
                        else
                          [ "bg-gray", "text-black", "opacity-50", "cursor-default" ]
                  )
              , onClick_ $ AskConfirmation namedAction
              , enabled isValid
              ]
              [ text "..." ]
          ]
      ]

renderAction _ isActiveParticipant (MakeNotify _) = div [] [ text "FIXME: awaiting observation?" ]

renderAction _ isActiveParticipant (Evaluate _) = div [] [ text "FIXME: what should we put here? Evaluate" ]

renderAction _ isActiveParticipant CloseContract =
  div_
    [ shortDescription isActiveParticipant "chocolate pastry apple pie lemon drops apple pie halvah FIXME"
    , button
        -- FIXME: adapt to use button classes from Css module
        [ classNames $ [ "font-bold", "w-full", "py-4", "mt-2", "rounded-lg", "shadow" ]
            <> if isActiveParticipant then
                [ "bg-gradient-to-r", "from-blue", "to-lightblue", "text-white" ]
              else
                [ "bg-gray", "text-black", "opacity-50", "cursor-default" ]
        , enabled isActiveParticipant
        , onClick_ $ AskConfirmation CloseContract
        ]
        [ text "Close contract" ]
    ]

currencyFormatter :: Formatter
currencyFormatter =
  Formatter
    { sign: false
    , before: 0
    , comma: true
    , after: 0
    , abbreviations: false
    }

formatBigInteger :: BigInteger -> String
formatBigInteger = format currencyFormatter <<< toNumber

currency :: forall p a. Token -> BigInteger -> HTML p a
currency (Token "" "") value = text ("₳ " <> formatBigInteger value)

currency (Token symbol _) value = text (symbol <> " " <> formatBigInteger value)

renderBalances :: forall p action. State -> HTML p action
renderBalances state =
  let
    accounts :: Array (Tuple (Tuple Party Token) BigInteger)
    accounts = Map.toUnfoldable $ state ^. (_executionState <<< _state <<< _accounts)

    -- FIXME: What should we show if a participant doesn't have balance yet?
    -- FIXME: We fake the accounts for development until we fix the semantics
    accounts' =
      [ (Role "alice" /\ Token "" "") /\ (fromInt 2500)
      , (Role "bob" /\ Token "" "") /\ (fromInt 10)
      ]
  in
    div [ classNames [ "text-xs" ] ]
      ( append
          [ div [ classNames [ "font-semibold", "py-3" ] ] [ text "Balance of accounts when the step was initiated." ]
          ]
          ( accounts'
              <#> ( \((party /\ token) /\ amount) ->
                    div [ classNames [ "flex", "justify-between", "py-3", "border-t" ] ]
                      [ span_ [ text $ participantWithNickname state party ]
                      , span [ classNames [ "font-semibold" ] ] [ currency token amount ]
                      ]
                )
          )
      )

shortDescription :: forall p. Boolean -> String -> HTML p Action
shortDescription isActiveParticipant description =
  div [ classNames ([ "text-xs" ] <> applyWhen (not isActiveParticipant) [ "opacity-50" ]) ]
    [ span [ classNames [ "font-semibold" ] ] [ text "Short description: " ]
    , span_ [ text description ]
    ]

getParty :: Input -> Maybe Party
getParty (IDeposit _ p _ _) = Just p

getParty (IChoice (ChoiceId _ p) _) = Just p

getParty _ = Nothing

{-
renderPastStep :: forall p. ExecutionStep -> HTML p Action
renderPastStep { state, timedOut: true } =
  let
    balances = renderBalances state
  in
    text ""

renderPastStep { txInput: TransactionInput { inputs }, state } =
  let
    balances = renderBalances state

    f :: Input -> Map (Maybe Party) (Array Input) -> Map (Maybe Party) (Array Input)
    f input acc = Map.insertWith append (getParty input) [ input ] acc

    inputsMap = foldr f mempty inputs

    tasks = renderCompletedTasks inputsMap
  in
    text ""

renderCompletedTasks :: forall p. Map (Maybe Party) (Array Input) -> HTML p Action
renderCompletedTasks inputsMap = text ""

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
-}
