module Contract.View
  ( contractCard
  , contractScreen
  , actionConfirmationCard
  ) where

import Prelude hiding (div)
import Contract.Lenses (_executionState, _metadata, _namedActions, _nickname, _participants, _pendingTransaction, _previousSteps, _selectedStep, _tab, _userParties)
import Contract.State (currentStep, isContractClosed)
import Contract.Types (Action(..), PreviousStep, PreviousStepState(..), State, Tab(..), scrollContainerRef)
import Css as Css
import Data.Array (foldr, intercalate, length)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.BigInteger (BigInteger, fromString)
import Data.Foldable (foldMap)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Lens ((^.))
import Data.Map (keys, lookup, toUnfoldable) as Map
import Data.Maybe (Maybe(..), isJust, maybe, maybe')
import Data.Set (Set)
import Data.Set as Set
import Data.String (take, trim)
import Data.String.Extra (capitalize)
import Data.Tuple (Tuple(..), fst, uncurry)
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Css (applyWhen, classNames)
import Halogen.Extra (lifeCycleEvent)
import Halogen.HTML (HTML, a, button, div, div_, h2, h3, h4_, input, p, span, span_, sup_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), enabled, href, id_, placeholder, ref, target, type_, value)
import Humanize (contractIcon, formatDate, formatTime, humanizeDuration, humanizeValue)
import LoadingSubmitButton.State (loadingSubmitButton)
import LoadingSubmitButton.Types (Message(..))
import MainFrame.Types (ChildSlots)
import Marlowe.Execution.Lenses (_semanticState, _mNextTimeout)
import Marlowe.Execution.State (expandBalances, getActionParticipant)
import Marlowe.Execution.Types (NamedAction(..))
import Marlowe.Extended (contractTypeName)
import Marlowe.Extended.Metadata (_contractType)
import Marlowe.PAB (transactionFee)
import Marlowe.Semantics (Accounts, Assets, Bound(..), ChoiceId(..), Input(..), Party(..), Slot, SlotInterval(..), Token, TransactionInput(..), getEncompassBound)
import Marlowe.Slot (secondsDiff, slotToDateTime)
import Material.Icons (Icon(..)) as Icon
import Material.Icons (icon, icon_)
import Popper (Placement(..))
import Tooltip.State (tooltip)
import Tooltip.Types (ReferenceId(..))
import WalletData.State (adaToken, getAda)

contractCard :: forall p. Slot -> State -> HTML p Action
contractCard currentSlot state =
  let
    currentStepNumber = (currentStep state) + 1

    nickname = state ^. _nickname

    contractType = state ^. (_metadata <<< _contractType)
  in
    div
      [ classNames [ "shadow", "bg-white", "rounded" ] ]
      [ div
          [ classNames [ "flex", "gap-2", "px-4", "py-2", "border-gray", "border-b" ] ]
          [ div
              [ classNames [ "flex-1" ] ]
              [ h3
                  [ classNames [ "flex", "gap-2", "items-center" ] ]
                  [ contractIcon contractType
                  , text $ contractTypeName contractType
                  ]
              , input
                  [ classNames $ Css.inputNoBorder <> [ "-ml-2", "text-lg" ]
                  , type_ InputText
                  , value nickname
                  , onValueInput_ SetNickname
                  , placeholder "Please rename"
                  ]
              ]
          , a
              [ classNames [ "flex", "items-center" ]
              , onClick_ SelectSelf
              ]
              [ icon Icon.ArrowRight [ "text-28px" ] ]
          ]
      , div
          [ classNames [ "px-4", "py-2", "border-gray", "border-b" ] ]
          [ p
              [ classNames [ "text-sm", "font-semibold" ] ]
              [ text $ "Current step:" <> show currentStepNumber ]
          , p
              [ classNames [ "font-semibold" ] ]
              [ text $ timeoutString currentSlot state ]
          ]
      , div
          [ classNames [ "h-dashboard-card-actions", "overflow-y-auto" ] ]
          [ currentStepActions currentSlot state ]
      ]

timeoutString :: Slot -> State -> String
timeoutString currentSlot state =
  let
    mNextTimeout = state ^. (_executionState <<< _mNextTimeout)
  in
    maybe'
      (\_ -> if isContractClosed state then "Contract closed" else "Timed out")
      (\nextTimeout -> humanizeDuration $ secondsDiff nextTimeout currentSlot)
      mNextTimeout

contractScreen :: forall m. MonadAff m => Slot -> State -> ComponentHTML Action ChildSlots m
contractScreen currentSlot state =
  let
    nickname = state ^. _nickname

    metadata = state ^. _metadata

    pastStepsCards = mapWithIndex (renderPastStep state) (state ^. _previousSteps)

    currentStepCard = [ renderCurrentStep currentSlot state ]

    -- NOTE: Because the cards container is a flex element with a max width property, when there are more cards than
    --       can fit the view, the browser will try shrink them and remove any extra right margin/padding (not sure
    --       why this is only done to the right side). To avoid our cards getting shrinked, we add the flex-shrink-0
    --       property, and we add an empty `div` that occupies space (aka also cant be shrinked) to allow that the
    --       first and last card can be scrolled to the center
    paddingElement = [ div [ classNames [ "flex-shrink-0", "-ml-3", "w-carousel-padding-element" ] ] [] ]
  in
    div
      [ classNames [ "flex", "flex-col", "items-center", "pt-5", "h-full" ]
      -- FIXME: This is causing problems with the tooltips
      , lifeCycleEvent { onInit: Just CarouselOpened, onFinalize: Just CarouselClosed }
      ]
      {- NOTE: The card is allowed to grow in an h-full container and the navigation buttons are absolute positioned
               because the cards x-scrolling can't coexist with a visible y-overflow. To avoid clipping the cards shadow
               we need the cards container to grow (hence the flex-grow). -}
      [ div [ classNames [ "flex-grow", "w-full" ] ]
          [ div
              [ classNames [ "flex", "items-center", "overflow-x-scroll", "h-full", "scrollbar-width-none", "relative" ]
              , ref scrollContainerRef
              ]
              (paddingElement <> pastStepsCards <> currentStepCard <> paddingElement)
          ]
      , cardNavigationButtons state
      -- TODO: Add a status indicator for the
      --  "Waiting for <participant>"
      --  "Contract starting"
      --  "Your turn"
      ]

cardNavigationButtons :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
cardNavigationButtons state =
  let
    lastStep = currentStep state

    selectedStep = state ^. _selectedStep

    contractIsClosed = isContractClosed state

    hasLeftStep = selectedStep > 0

    hasRightStep = selectedStep < lastStep

    buttonClasses isActive = [ "leading-none", "text-xl" ] <> applyWhen (not isActive) [ "text-darkgray", "cursor-none" ]

    leftButton =
      [ button
          [ classNames $ buttonClasses hasLeftStep
          , onClick \_ -> if hasLeftStep then (Just $ MoveToStep $ selectedStep - 1) else Nothing
          , enabled hasLeftStep
          , id_ "previousStepButton"
          ]
          [ icon_ Icon.ArrowLeft ]
      , tooltip "Previous step" (RefId "previousStepButton") Bottom
      ]

    rightButton =
      [ button
          [ classNames $ buttonClasses hasRightStep
          , onClick \_ -> if hasRightStep then (Just $ MoveToStep $ selectedStep + 1) else Nothing
          , enabled hasRightStep
          , id_ "nextStepButton"
          ]
          [ icon_ Icon.ArrowRight ]
      , tooltip "Next step" (RefId "nextStepButton") Bottom
      ]
  in
    div [ classNames [ "mb-6", "flex", "items-center", "px-6", "py-2", "bg-white", "rounded", "shadow" ] ]
      $ leftButton
      <> [ icon Icon.Info [ "px-4", "invisible" ] ]
      <> rightButton

-- TODO: This is a lot like the `contractSetupConfirmationCard` in `Template.View`. Consider factoring out a shared component.
actionConfirmationCard ::
  forall m.
  MonadAff m =>
  Assets ->
  NamedAction ->
  State ->
  ComponentHTML Action ChildSlots m
actionConfirmationCard assets namedAction state =
  let
    stepNumber = currentStep state

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

    transactionFeeItem = detailItem [ text "Transaction fee", sup_ [ text "*" ], text ":" ] [ text $ humanizeValue adaToken transactionFee ]

    actionAmountItems = case namedAction of
      MakeDeposit _ _ token amount ->
        [ detailItem [ text "Deposit amount:" ] [ text $ humanizeValue token amount ] false
        , transactionFeeItem true
        ]
      MakeChoice _ _ (Just option) ->
        [ detailItem [ text "You are choosing:" ] [ text $ "[ option " <> show option <> " ]" ] false
        , transactionFeeItem true
        ]
      _ -> [ transactionFeeItem false ]

    -- TODO: when we allow custom currency other than ada, we won't be able to add the deposit amount
    -- to the transaction fee (always in ada)
    totalToPay = case namedAction of
      MakeDeposit _ _ _ amount -> amount + transactionFee
      _ -> transactionFee

    hasSufficientFunds = getAda assets >= totalToPay
  in
    div_
      [ div [ classNames [ "flex", "font-semibold", "justify-between", "bg-lightgray", "p-5" ] ]
          [ span_ [ text "Demo wallet balance:" ]
          , span_ [ text $ humanizeValue adaToken $ getAda assets ]
          ]
      , div [ classNames [ "px-5", "pb-6", "pt-3", "md:pb-8" ] ]
          [ h2
              [ classNames [ "text-xl", "font-semibold" ] ]
              [ text $ "Step " <> show (stepNumber + 1) ]
          , h3
              [ classNames [ "text-xs", "font-semibold" ] ]
              [ text title ]
          , div [ classNames [ "flex", "border-b", "border-gray", "mt-4" ] ]
              actionAmountItems
          , h3
              [ classNames [ "mt-4", "text-sm", "font-semibold" ] ]
              [ text "Confirm payment of:" ]
          , div
              [ classNames [ "mb-4", "text-purple", "font-semibold", "text-2xl" ] ]
              [ text $ humanizeValue adaToken totalToPay ]
          , div [ classNames [ "flex", "justify-center" ] ]
              [ button
                  [ classNames $ Css.secondaryButton <> [ "mr-2", "flex-1" ]
                  , onClick_ CancelConfirmation
                  ]
                  [ text "Cancel" ]
              , loadingSubmitButton
                  { ref: "action-confirm-button"
                  , caption: cta
                  , styles: [ "flex-1" ]
                  , enabled: hasSufficientFunds
                  , handler:
                      \msg -> case msg of
                        OnSubmit -> Just $ ConfirmAction namedAction
                        _ -> Nothing
                  }
              ]
          , div
              [ classNames [ "my-4", "text-sm", "text-red" ] ]
              if hasSufficientFunds then
                []
              else
                [ text "You have insufficient funds to complete this transaction." ]
          , div [ classNames [ "bg-black", "text-white", "p-4", "mt-4", "rounded" ] ]
              [ h3 [ classNames [ "text-sm", "font-semibold" ] ] [ sup_ [ text "*" ], text "Transaction fees are estimates only:" ]
              , p [ classNames [ "pb-4", "border-b-half", "border-lightgray", "text-xs", "text-gray" ] ]
                  -- FIXME: review text with simon
                  [ text "In the demo all fees are fixed at 10 lovelace, but in the live version the cost will depend on the status of the blockchain at the moment of the transaction." ]
              , div [ classNames [ "pt-4", "flex", "justify-between", "items-center" ] ]
                  [ a
                      -- FIXME: where should this link point to?
                      [ href "https://docs.cardano.org/en/latest/explore-cardano/cardano-fee-structure.html"
                      , classNames [ "font-bold" ]
                      , target "_blank"
                      ]
                      [ text "Read more in Docs" ]
                  , icon Icon.ArrowRight [ "text-2xl" ]
                  ]
              ]
          ]
      ]

renderContractCard :: forall p. Int -> State -> Tab -> Array (HTML p Action) -> HTML p Action
renderContractCard stepNumber state currentTab cardBody =
  let
    tabSelector isActive =
      [ "flex-grow", "text-center", "py-2", "trapesodial-card-selector", "text-sm", "font-semibold" ]
        <> case isActive of
            true -> [ "active" ]
            false -> []

    contractCardCss =
      -- NOTE: The cards that are not selected gets scaled down to 77 percent of the original size. But when you scale down
      --       an element with CSS transform property, the parent still occupies the same layout dimensions as before,
      --       so the perceived margins are bigger than we'd want to. To solve this we add negative margin of 4
      --       to the "not selected" cards, a positive margin of 2 to the selected one
      -- Base classes
      [ "grid", "grid-rows-auto-1fr", "rounded", "overflow-hidden", "flex-shrink-0", "w-contract-card", "h-contract-card", "transform", "transition-transform", "duration-100", "ease-out", "mb-8", "filter" ]
        <> if (state ^. _selectedStep /= stepNumber) then
            -- Not selected card modifiers
            [ "drop-shadow", "scale-77", "-mx-4" ]
          else
            -- Selected card modifiers
            [ "drop-shadow-lg", "mx-2" ]
  in
    div [ classNames contractCardCss ]
      [ div [ classNames [ "flex", "select-none" ] ]
          [ a
              [ classNames (tabSelector $ currentTab == Tasks)
              , onClick_ $ SelectTab stepNumber Tasks
              ]
              [ span_ $ [ text "Tasks" ] ]
          , a
              [ classNames (tabSelector $ currentTab == Balances)
              , onClick_ $ SelectTab stepNumber Balances
              ]
              [ span_ $ [ text "Balances" ] ]
          ]
      , div [ classNames [ "bg-white", "grid", "grid-rows-auto-1fr" ] ] cardBody
      ]

renderPastStep :: forall p. State -> Int -> PreviousStep -> HTML p Action
renderPastStep state stepNumber step =
  let
    currentTab = step ^. _tab

    renderBody Tasks { state: TransactionStep txInput } = renderPastActions state txInput

    renderBody Tasks { state: TimeoutStep timeoutSlot } = renderTimeout stepNumber timeoutSlot

    renderBody Balances { balances } = renderBalances state balances

    statusIndicator stepState =
      div
        [ classNames $ [ "h-10", "flex", "items-center" ] ]
        $ case stepState of
            TimeoutStep _ ->
              [ span
                  [ classNames [ "select-none", "font-semibold" ] ]
                  [ text "Timed out" ]
              , icon Icon.Timer [ "pl-2" ]
              ]
            TransactionStep _ ->
              [ icon Icon.Done [ "text-green" ]
              , span
                  [ classNames [ "pl-2", "select-none", "font-semibold", "text-green" ] ]
                  [ text "Completed" ]
              ]
  in
    renderContractCard stepNumber state currentTab
      [ div [ classNames [ "py-2.5", "px-4", "flex", "items-center", "border-b", "border-lightgray" ] ]
          [ span
              [ classNames [ "text-xl", "font-semibold", "flex-grow" ] ]
              [ text $ "Step " <> show (stepNumber + 1) ]
          , statusIndicator step.state
          ]
      , div [ classNames [ "overflow-y-auto", "px-4", "bg-gray" ] ]
          [ renderBody currentTab step
          ]
      ]

type InputsByParty
  = { inputs :: Array Input, interval :: SlotInterval, party :: Party }

-- Normally we would expect that a TransactionInput has either no inputs or a single one
-- but the types allows for them to be a list of different inputs, possibly made by different
-- parties. If there are multiple inputs we group them by participant.
groupTransactionInputByParticipant :: TransactionInput -> Array InputsByParty
groupTransactionInputByParticipant (TransactionInput { inputs, interval }) =
  Array.fromFoldable inputs
    # Array.mapMaybe
        ( \input -> getParty input <#> (\party -> { inputs: [ input ], party })
        )
    # Array.groupBy sameParty
    # map mergeInputsFromSameParty
  where
  sameParty a b = a.party == b.party

  mergeInputsFromSameParty ::
    NonEmptyArray { inputs :: Array Input, party :: Party } ->
    InputsByParty
  mergeInputsFromSameParty elements =
    foldr
      (\elem accu -> accu { inputs = elem.inputs <> accu.inputs })
      (NonEmptyArray.head elements # \{ party } -> { inputs: [], party, interval })
      elements

renderPastActions :: forall p a. State -> TransactionInput -> HTML p a
renderPastActions state txInput =
  let
    actionsByParticipant = groupTransactionInputByParticipant txInput
  in
    div_
      $ if Array.length actionsByParticipant == 0 then
          -- TODO: See if we can reach this state and what text describes it better.
          [ text "An empty transaction was made to advance this step" ]
        else
          renderPartyPastActions state <$> actionsByParticipant

renderPartyPastActions :: forall p a. State -> InputsByParty -> HTML p a
renderPartyPastActions state { inputs, interval, party } =
  let
    -- We don't know exactly when a transaction was executed, we have an interval. But
    -- the design asks for an exact date so we use the lower end of the interval so that
    -- we don't show a value in the future
    (SlotInterval intervalFrom _) = interval

    -- TODO: This time is in UTC, we need to localize.
    mTransactionDateTime = slotToDateTime intervalFrom

    transactionDate = maybe "-" formatDate mTransactionDateTime

    transactionTime = maybe "-" formatTime mTransactionDateTime

    renderPartyHeader =
      div [ classNames [ "flex", "justify-between", "items-center", "border-b", "border-gray", "px-3", "pb-4" ] ]
        [ renderParty [] state party
        , div [ classNames [ "flex", "flex-col", "items-end", "text-xs" ] ]
            [ span [] [ text $ transactionDate ]
            , span [ classNames [ "font-semibold" ] ] [ text transactionTime ]
            ]
        ]

    renderFeesSummary =
      div [ classNames [ "pt-4", "px-3", "border-t", "border-gray", "flex", "items-center", "text-xs" ] ]
        [ icon Icon.Language [ "text-lightpurple", "text-lg", "mr-1" ]
        , span [ classNames [ "font-semibold" ] ]
            [ text "Total fees:"
            ]
        , span [ classNames [ "flex-grow", "text-right" ] ] [ text $ humanizeValue adaToken transactionFee ]
        ]

    renderActionsBody =
      div [ classNames [ "py-4", "px-3" ] ]
        (map renderPastAction inputs)

    renderPastAction = case _ of
      IDeposit intoAccountOf by token value -> renderDeposit state intoAccountOf by token value
      IChoice (ChoiceId choiceIdKey _) chosenNum ->
        div []
          [ h4_ [ text "Chose:" ]
          -- NOTE: It would be neat if we could use the same trick that we use in renderAction.MakeChoice
          --       to detect if this is a single option or not, but we don't have the bounds of the choice
          --       available here. We could later add a way to get that from the contract or rethink the
          --       different constructs of When to properly include a single option and an enum.
          , span_ [ text $ show chosenNum <> " for " ]
          , span [ classNames [ "font-semibold" ] ] [ text choiceIdKey ]
          ]
      _ -> div_ []
  in
    div [ classNames [ "mt-4", "bg-white", "rounded", "shadow-sm", "py-4" ] ]
      [ renderPartyHeader
      , renderActionsBody
      , renderFeesSummary
      ]

renderTimeout :: forall p a. Int -> Slot -> HTML p a
renderTimeout stepNumber timeoutSlot =
  let
    timedOutDate =
      maybe
        "invalid date"
        (\dt -> formatDate dt <> " at " <> formatTime dt)
        (slotToDateTime timeoutSlot)
  in
    div [ classNames [ "flex", "flex-col", "items-center" ] ]
      -- NOTE: we use pt-16 instead of making the parent justify-center because in the design it's not actually
      --       centered and it has more space above than below.
      [ icon Icon.Timer [ "pb-2", "pt-16", "text-red", "text-big-icon" ]
      , span [ classNames [ "font-semibold", "text-center", "text-sm" ] ]
          [ text $ "Step " <> show (stepNumber + 1) <> " timed out on " <> timedOutDate ]
      ]

renderCurrentStep :: forall p. Slot -> State -> HTML p Action
renderCurrentStep currentSlot state =
  let
    stepNumber = currentStep state

    currentTab = state ^. _tab

    pendingTransaction = state ^. _pendingTransaction

    contractIsClosed = isContractClosed state

    mNextTimeout = state ^. (_executionState <<< _mNextTimeout)

    statusIndicator mIcon status =
      div
        [ classNames $ [ "flex-grow", "h-10", "flex", "items-center" ] ]
        $ Array.catMaybes
            [ Just $ span [ classNames [ "select-none", "text-base", "flex-grow", "text-right", "font-semibold" ] ] [ text status ]
            , mIcon <#> \anIcon -> icon anIcon [ "pl-2" ]
            ]
  in
    renderContractCard stepNumber state currentTab
      [ div [ classNames [ "py-2.5", "px-4", "flex", "items-center", "border-b", "border-lightgray" ] ]
          [ span
              [ classNames [ "text-xl", "font-semibold", "flex-grow" ] ]
              [ text $ "Step " <> show (stepNumber + 1) ]
          , case contractIsClosed, isJust pendingTransaction of
              true, _ -> statusIndicator Nothing "Contract closed"
              _, true -> statusIndicator Nothing "Awaiting confirmation"
              _, _ -> statusIndicator (Just Icon.Timer) (timeoutString currentSlot state)
          ]
      , div
          [ classNames [ "overflow-y-auto" ] ]
          [ currentStepActions currentSlot state ]
      ]

currentStepActions :: forall p. Slot -> State -> HTML p Action
currentStepActions currentSlot state =
  let
    currentTab = state ^. _tab

    pendingTransaction = state ^. _pendingTransaction

    participants = state ^. _participants

    semanticState = state ^. (_executionState <<< _semanticState)

    balances = expandBalances (Set.toUnfoldable $ Map.keys participants) [ adaToken ] semanticState
  in
    case currentTab, isContractClosed state, isJust pendingTransaction of
      Tasks, true, _ -> renderContractClose
      Tasks, _, true -> renderPendingStep
      Tasks, _, _ -> renderTasks state
      Balances, _, _ -> renderBalances state balances

renderContractClose :: forall p a. HTML p a
renderContractClose =
  div [ classNames [ "h-full", "flex", "flex-col", "justify-center", "items-center", "p-4" ] ]
    [ icon Icon.TaskAlt [ "text-green", "text-big-icon" ]
    , div
        -- The bottom margin on this div means the whole thing isn't perfectly centered vertically.
        -- Because there's an image on top and text below, being perfectly centered vertically
        -- looks wrong.
        [ classNames [ "text-center", "text-sm", "mb-4" ] ]
        [ div [ classNames [ "font-semibold" ] ]
            [ text "This contract is now closed" ]
        , div_ [ text "There are no tasks to complete" ]
        ]
    ]

-- FIXME: when we have a design for this, we can include more information (probably making this look more like
-- the past step card)
renderPendingStep :: forall p a. HTML p a
renderPendingStep =
  div [ classNames [ "px-4", "mt-4" ] ]
    [ text "Your transaction has been submitted. You will be notified when confirmation is received." ]

-- This helper function expands actions that can be taken by anybody,
-- then groups by participant and sorts it so that the owner starts first and the rest go
-- in alphabetical order
expandAndGroupByRole ::
  Set Party ->
  Set Party ->
  Array NamedAction ->
  Array (Tuple Party (Array NamedAction))
expandAndGroupByRole userParties allParticipants actions =
  expandedActions
    # Array.sortBy currentPartiesFirst
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

  currentPartiesFirst (Tuple party1 _) (Tuple party2 _)
    | Set.member party1 userParties = LT
    | Set.member party2 userParties = GT
    | otherwise = compare party1 party2

  sameParty a b = fst a == fst b

  extractGroupedParty :: NonEmptyArray (Tuple Party NamedAction) -> Tuple Party (Array NamedAction)
  extractGroupedParty group = case NonEmptyArray.unzip group of
    tokens /\ actions' -> NonEmptyArray.head tokens /\ NonEmptyArray.toArray actions'

renderTasks :: forall p. State -> HTML p Action
renderTasks state =
  let
    executionState = state ^. _executionState

    userParties = state ^. _userParties

    actions = state ^. _namedActions

    expandedActions =
      expandAndGroupByRole
        userParties
        (Map.keys $ state ^. _participants)
        actions
  in
    if length expandedActions > 0 then
      div
        [ classNames [ "px-4", "pb-4" ] ]
        $ expandedActions
        <#> uncurry (renderPartyTasks state)
    else
      div
        [ classNames [ "p-4" ] ]
        [ text "There are no tasks to perform at this step. The contract will progress automatically when the timeout has passed." ]

participantWithNickname :: State -> Party -> String
participantWithNickname state party =
  let
    mNickname :: Maybe String
    mNickname = join $ Map.lookup party (state ^. _participants)
  in
    capitalize case party, mNickname of
      -- TODO: For the demo we wont have PK, but eventually we probably want to limit the amount of characters
      PK publicKey, _ -> publicKey
      Role roleName, Just nickname -> roleName <> " (" <> nickname <> ")"
      Role roleName, Nothing -> roleName

renderDeposit :: State -> Party -> Party -> Token -> BigInteger -> forall p a. HTML p a
renderDeposit state to from token value =
  div [ classNames [ "flex", "flex-col" ] ]
    -- FIXME: The designs makes the distinction between Wallet and account, but a party is either
    --        PK or Role, so we may need to rethink this part.
    [ renderParty [] state from
    , div [ classNames [ "flex", "justify-between", "items-center" ] ]
        [ icon Icon.South [ "text-purple", "text-xs", "ml-1" ]
        , span [ classNames [ "text-xs", "text-green" ] ] [ text $ humanizeValue token value ]
        ]
    , renderParty [] state to
    ]

firstLetterInCircle :: forall p a. Array String -> String -> HTML p a
firstLetterInCircle colorStyles name =
  div
    [ classNames
        $ [ "bg-gradient-to-r"
          , "from-purple"
          , "to-lightpurple"
          , "text-white"
          , "rounded-full"
          , "w-5"
          , "h-5"
          , "text-center"
          , "mr-1"
          , "font-semibold"
          ]
        <> colorStyles
    ]
    [ text $ take 1 name ]

-- TODO: In zeplin all participants have a different color. We need to decide how are we going to assing
--       colors to users. For now they all have purple
renderParty :: forall p a. Array String -> State -> Party -> HTML p a
renderParty styles state party =
  let
    participantName = participantWithNickname state party

    userParties = state ^. _userParties
  in
    div [ classNames $ [ "text-xs", "flex" ] <> styles ]
      [ firstLetterInCircle [ "bg-gradient-to-r", "from-purple", "to-lightpurple", "text-white" ] participantName
      , div [ classNames [ "font-semibold" ] ]
          [ text $ if Set.member party userParties then participantName <> " (you)" else participantName
          ]
      ]

renderPartyTasks :: forall p. State -> Party -> Array NamedAction -> HTML p Action
renderPartyTasks state party actions =
  let
    actionsSeparatedByOr =
      intercalate
        [ div [ classNames [ "font-semibold", "text-center", "my-2", "text-xs" ] ] [ text "OR" ]
        ]
        (Array.singleton <<< renderAction state party <$> actions)
  in
    div [ classNames [ "mt-3" ] ]
      ([ renderParty [ "mb-2" ] state party ] <> actionsSeparatedByOr)

-- FIXME: This was added to allow anybody being able to do any actions for debug purposes...
--        Remove once the PAB is connected
debugMode :: Boolean
debugMode = false

-- The Party parameter represents who is taking the action
renderAction :: forall p. State -> Party -> NamedAction -> HTML p Action
renderAction state party namedAction@(MakeDeposit intoAccountOf by token value) =
  let
    userParties = state ^. _userParties

    isActiveParticipant = Set.member party userParties

    fromDescription =
      if isActiveParticipant then
        "You make"
      else case party of
        PK publicKey -> "Account " <> publicKey <> " makes"
        Role roleName -> capitalize roleName <> " makes"

    toDescription =
      if Set.member intoAccountOf userParties then
        "your"
      else
        if by == intoAccountOf then
          "their"
        else case intoAccountOf of
          PK publicKey -> publicKey <> " public key"
          Role roleName -> roleName <> "'s"

    description = fromDescription <> " a deposit into " <> toDescription <> " account"
  in
    div_
      [ shortDescription isActiveParticipant description
      , button
          [ classNames $ Css.button <> Css.withAnimation <> [ "flex", "justify-between", "w-full", "mt-2" ]
              <> if isActiveParticipant || debugMode then
                  Css.bgBlueGradient <> Css.withShadow
                else
                  [ "text-black", "cursor-default" ]
          , enabled $ isActiveParticipant || debugMode
          , onClick_ $ AskConfirmation namedAction
          ]
          [ span_ [ text "Deposit:" ]
          , span_ [ text $ humanizeValue token value ]
          ]
      ]

renderAction state party namedAction@(MakeChoice choiceId bounds mChosenNum) =
  let
    userParties = state ^. _userParties

    isActiveParticipant = Set.member party userParties

    metadata = state ^. _metadata

    -- NOTE': We could eventually add an heuristic that if the difference between min and max is less
    --        than 10 elements, we could show a `select` instead of a input[number]
    Bound minBound maxBound = getEncompassBound bounds

    ChoiceId choiceIdKey _ = choiceId

    choiceDescription = case Map.lookup choiceIdKey metadata.choiceInfo of
      Just { choiceDescription: description }
        | trim description /= "" -> shortDescription isActiveParticipant description
      _ -> div_ []

    isValid = maybe false (between minBound maxBound) mChosenNum

    multipleInput = \_ ->
      div
        [ classNames
            $ [ "flex"
              , "w-full"
              , "rounded"
              , "mt-2"
              , "overflow-hidden"
              , "focus-within:ring-1"
              , "ring-black"
              ]
            <> applyWhen (isActiveParticipant || debugMode) Css.withShadow
        ]
        [ input
            [ classNames [ "border-0", "py-4", "pl-4", "pr-1", "flex-grow", "focus:ring-0", "min-w-0", "text-sm", "disabled:bg-lightgray" ]
            , type_ InputNumber
            , enabled $ isActiveParticipant || debugMode
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
                        Css.bgBlueGradient
                      else
                        [ "bg-darkgray", "text-white", "opacity-50", "cursor-default" ]
                )
            , onClick_ $ AskConfirmation namedAction
            , enabled $ isValid && isActiveParticipant
            ]
            [ text "..." ]
        ]

    singleInput = \_ ->
      button
        [ classNames $ Css.button <> Css.withAnimation <> [ "w-full", "mt-2" ]
            <> if isActiveParticipant || debugMode then
                Css.bgBlueGradient <> Css.withShadow
              else
                [ "text-black", "cursor-default" ]
        , enabled $ isActiveParticipant || debugMode
        , onClick_ $ AskConfirmation $ MakeChoice choiceId bounds $ Just minBound
        ]
        [ span_ [ text choiceIdKey ]
        ]
  in
    div_
      [ choiceDescription
      , if minBound == maxBound then
          singleInput unit
        else
          multipleInput unit
      ]

renderAction _ _ (MakeNotify _) = div [] [ text "FIXME: awaiting observation?" ]

renderAction _ _ (Evaluate _) = div [] [ text "FIXME: what should we put here? Evaluate" ]

renderAction state party CloseContract =
  let
    userParties = state ^. _userParties

    isActiveParticipant = Set.member party userParties
  in
    div_
      -- FIXME: revisit the text
      [ shortDescription isActiveParticipant "The contract is still open and needs to be manually closed by any participant for the remainder of the balances to be distributed (charges may apply)"
      , button
          -- TODO: adapt to use button classes from Css module
          [ classNames $ Css.button <> Css.withAnimation <> [ "w-full", "mt-2" ]
              <> if isActiveParticipant || debugMode then
                  Css.bgBlueGradient <> Css.withShadow
                else
                  [ "text-black", "cursor-default" ]
          , enabled $ isActiveParticipant || debugMode
          , onClick_ $ AskConfirmation CloseContract
          ]
          [ text "Close contract" ]
      ]

renderBalances :: forall p a. State -> Accounts -> HTML p a
renderBalances state accounts =
  let
    -- TODO: Right now we only have one type of Token (ada), but when we support multiple tokens we may want to group by
    --       participant and show the different tokens for each participant.
    accounts' :: Array (Tuple (Tuple Party Token) BigInteger)
    accounts' = Map.toUnfoldable accounts
  in
    div [ classNames [ "text-xs" ] ]
      ( append
          [ div [ classNames [ "font-semibold", "py-3" ] ] [ text "Balance of accounts when the step was initiated." ]
          ]
          ( accounts'
              <#> ( \((party /\ token) /\ amount) ->
                    div [ classNames [ "flex", "justify-between", "py-3", "border-t" ] ]
                      [ span_ [ text $ participantWithNickname state party ]
                      , span [ classNames [ "font-semibold" ] ] [ text $ humanizeValue token amount ]
                      ]
                )
          )
      )

shortDescription :: forall p a. Boolean -> String -> HTML p a
shortDescription isActiveParticipant description =
  div [ classNames ([ "text-xs" ] <> applyWhen (not isActiveParticipant) [ "opacity-50" ]) ]
    [ span [ classNames [ "font-semibold" ] ] [ text "Short description: " ]
    , span_ [ text description ]
    ]

getParty :: Input -> Maybe Party
getParty (IDeposit _ p _ _) = Just p

getParty (IChoice (ChoiceId _ p) _) = Just p

getParty _ = Nothing
