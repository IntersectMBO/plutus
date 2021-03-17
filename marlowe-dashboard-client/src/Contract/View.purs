module Contract.View
  ( contractDetailsCard
  ) where

import Prelude hiding (div)
import Contract.Lenses (_executionState, _mActiveUserParty, _metadata, _participants, _step, _tab)
import Contract.Types (Action(..), State, Tab(..))
import Css (applyWhen, classNames)
import Css as Css
import Data.Array (intercalate, nub, range)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.BigInteger (BigInteger, fromInt, toNumber)
import Data.Foldable (foldMap)
import Data.Int (floor)
import Data.Lens ((^.))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.String.Extra (capitalize)
import Data.Tuple (Tuple(..), fst, uncurry)
import Data.Tuple.Nested ((/\))
import Halogen.HTML (HTML, a, button, div, div_, h1, h2, option_, select, span, span_, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (enabled)
import Marlowe.Execution (NamedAction(..), _contract, _namedActions, _state, getActionParticipant)
import Marlowe.Extended (contractTypeName)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Input(..), Party(..), Token(..), _accounts)
import Material.Icons (Icon(..), icon)

contractDetailsCard :: forall p. State -> HTML p Action
contractDetailsCard state =
  let
    metadata = state ^. _metadata
  in
    div [ classNames [ "flex", "flex-col", "items-center", "mt-5" ] ]
      [ h1 [ classNames [ "text-xl", "font-semibold" ] ] [ text metadata.contractName ]
      -- FIXME: in zeplin the contractType is defined with color #283346, we need to define
      --        the color palette with russ.
      , h2 [ classNames [ "mb-2", "text-xs", "uppercase" ] ] [ text $ contractTypeName metadata.contractType ]
      , div [ classNames [ "w-full", "px-5", "max-w-contract-card" ] ] [ renderCurrentState state ]
      ]

renderCurrentState :: forall p. State -> HTML p Action
renderCurrentState state =
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
                  [ classNames [ "flex-grow", "rounded", "bg-lightgray", "py-2", "flex", "items-center" ] ]
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

    -- FIXME: We fake the namedActions for development until we fix the semantics
    actions' =
      [ MakeDeposit (Role "into account") (Role "bob") (Token "" "") $ fromInt 200
      , MakeDeposit (Role "into account") (Role "alice") (Token "" "") $ fromInt 1500
      , MakeChoice (ChoiceId "choice id" (Role "alice"))
          [ Bound (fromInt 0) (fromInt 3)
          , Bound (fromInt 2) (fromInt 4)
          , Bound (fromInt 6) (fromInt 8)
          ]
          (fromInt 0)
      , CloseContract
      ]

    expandedActions =
      expandAndGroupByRole
        (state ^. _mActiveUserParty)
        (Map.keys $ state ^. _participants)
        actions'

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
        (Array.singleton <<< renderAction isActiveParticipant <$> actions)

    participantName = participantWithNickname state party
  in
    div [ classNames [ "mt-3" ] ]
      ( [ div [ classNames [ "text-xs", "flex", "mb-2" ] ]
            -- TODO: In zeplin all participants have a different color. We need to decide how are we going to assing
            --       colors to users. For now they all have blue
            [ div [ classNames [ "bg-gradient-to-r", "from-blue", "to-lightblue", "text-white", "rounded-full", "w-4", "h-4", "text-center", "mr-1" ] ] [ text $ String.take 1 participantName ]
            , div [ classNames [ "font-semibold" ] ] [ text participantName ]
            ]
        ]
          <> actionsSeparatedByOr
      )

renderAction :: forall p. Boolean -> NamedAction -> HTML p Action
renderAction isActiveParticipant (MakeDeposit intoAccountOf by token value) =
  div_
    [ shortDescription isActiveParticipant "chocolate pastry apple pie lemon drops apple pie halvah FIXME"
    , button
        [ classNames $ [ "w-full", "flex", "justify-between", "mt-2" ]
            <> if isActiveParticipant then
                Css.primaryButton
              else
                Css.secondaryButton
        , enabled isActiveParticipant
        -- FIXME
        -- , onClick_ $ NEEDACTION
        ]
        [ span_ [ text "Deposit:" ]
        -- FIXME: Install purescript-formatters to separate by thousands
        , span_ [ currency token value ]
        ]
    ]

renderAction isActiveParticipant (MakeChoice choiceId bounds chosen) =
  let
    bigNumberToInt = floor <<< toNumber

    options :: Array Int
    options =
      nub
        $ bounds
        >>= \(Bound fromB toB) -> range (bigNumberToInt fromB) (bigNumberToInt toB)
  in
    div_
      [ shortDescription isActiveParticipant "chocolate pastry apple pie lemon drops apple pie halvah FIXME"
      -- FIXME: we need to use @tailwindcss/forms to reset forms inputs and then restyle
      --        https://www.youtube.com/watch?v=pONeWAzDsQg&ab_channel=TailwindLabs
      , select
          [ classNames [ "w-full", "py-4", "px-4", "shadow", "rounded-3xl", "mt-2" ]
          , enabled isActiveParticipant
          -- FIXME: I need to rethink how to make this select. The option items do not have
          --        an onChange event, at most an onClick, which is probably not what I want
          --        and I need to get the chosen value.
          -- , onChange
          --     $ \ev -> do
          --         let
          --           ww = spy "Event" ev
          --         trg <- target ev
          --         let
          --           xx = spy "target" trg
          --         -- value :: HTMLSelectElement -> Effect String
          --         Just $ ChangeChoice choiceId (fromInt 1)
          ]
          (options <#> \n -> option_ [ text $ show n ])
      ]

renderAction isActiveParticipant (MakeNotify _) = div [] [ text "awaiting observation?" ]

renderAction isActiveParticipant (Evaluate _) = div [] [ text "FIXME: what should we put here? Evaluate" ]

renderAction isActiveParticipant CloseContract =
  div_
    [ shortDescription isActiveParticipant "chocolate pastry apple pie lemon drops apple pie halvah FIXME"
    , button
        [ classNames
            $ [ "w-full", "flex", "justify-between", "mt-2" ]
            <> if isActiveParticipant then
                Css.primaryButton
              else
                Css.secondaryButton
        , enabled isActiveParticipant
        -- FIXME
        -- , onClick_ $ NEEDACTION
        ]
        [ text "Close contract" ]
    ]

currency :: forall p a. Token -> BigInteger -> HTML p a
currency (Token "" "") value = text ("₳" <> show value)

currency (Token symbol _) value = text (symbol <> show value)

renderBalances :: forall p action. State -> HTML p action
renderBalances state =
  let
    accounts :: Array (Tuple (Tuple Party Token) BigInteger)
    accounts = Map.toUnfoldable $ state ^. (_executionState <<< _state <<< _accounts)

    -- FIXME: What should we show if a participant doesn't have balance yet?
    -- FIXME: We fake the accounts for development until we fix the semantics
    accounts' =
      [ (Role "alice" /\ Token "" "") /\ (fromInt 500)
      , (Role "bob" /\ Token "" "") /\ (fromInt 0)
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
