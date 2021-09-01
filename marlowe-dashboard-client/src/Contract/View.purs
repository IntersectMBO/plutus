module Contract.View
  ( contractPreviewCard
  , contractScreen
  , actionConfirmationCard
  ) where

import Prelude hiding (div)
import Contract.Lenses (_executionState, _expandPayments, _metadata, _namedActions, _nickname, _participants, _pendingTransaction, _previousSteps, _resultingPayments, _selectedStep, _tab, _userParties)
import Contract.State (currentStep, isContractClosed)
import Contract.Types (Action(..), Input, Movement(..), PreviousStep, PreviousStepState(..), State, StepBalance, Tab(..), TimeoutInfo, scrollContainerRef)
import Css as Css
import Data.Array (foldr, intercalate, length)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.BigInteger (BigInteger, fromString)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Lens (set, (^.))
import Data.Map (intersectionWith, keys, lookup, toUnfoldable) as Map
import Data.Maybe (Maybe(..), isJust, maybe, maybe')
import Data.Set as Set
import Data.String (take, trim)
import Data.String.Extra (capitalize)
import Data.Tuple (Tuple, fst, uncurry)
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Css (applyWhen, classNames)
import Halogen.Extra (lifeCycleSlot, LifecycleEvent(..))
import Halogen.HTML (HTML, a, button, div, div_, h2, h3, h4, h4_, input, p, span, span_, sup_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), enabled, href, id_, placeholder, ref, target, type_, value)
import Hint.State (hint)
import Humanize (contractIcon, formatDate, formatTime, humanizeDuration, humanizeOffset, humanizeValue)
import LoadingSubmitButton.State (loadingSubmitButton)
import LoadingSubmitButton.Types (Message(..))
import MainFrame.Types (ChildSlots)
import Marlowe.Execution.Lenses (_semanticState, _mNextTimeout)
import Marlowe.Execution.State (expandBalances)
import Marlowe.Execution.Types (NamedAction(..))
import Marlowe.Extended (contractTypeName)
import Marlowe.Extended.Metadata (_contractType)
import Marlowe.PAB (transactionFee)
import Marlowe.Semantics (Assets, Bound(..), ChoiceId(..), Party(..), Payee(..), Payment(..), Slot, SlotInterval(..), Token, TransactionInput(..), _accounts, getEncompassBound)
import Marlowe.Semantics (Input(..)) as S
import Marlowe.Slot (secondsDiff, slotToDateTime)
import Material.Icons (Icon(..)) as Icon
import Material.Icons (icon, icon_)
import Popper (Placement(..))
import Tooltip.State (tooltip)
import Text.Markdown.TrimmedInline (markdownToHTML)
import Tooltip.Types (ReferenceId(..))
import WalletData.State (adaToken, getAda)

-- This card shows a preview of the contract (intended to be used in the dashboard)
contractPreviewCard :: forall m. MonadAff m => Slot -> State -> ComponentHTML Action ChildSlots m
contractPreviewCard currentSlot state =
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
          -- NOTE: We use a slightly modification of the state here in order
          --       to ensure that the preview card always shows the Task tab
          --       and not the balance tab.
          [ currentStepActions currentStepNumber $ set _tab Tasks state ]
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

contractScreen :: forall m. MonadAff m => Input -> State -> ComponentHTML Action ChildSlots m
contractScreen viewInput state =
  let
    nickname = state ^. _nickname

    metadata = state ^. _metadata

    pastStepsCards = mapWithIndex (renderPastStep viewInput state) (state ^. _previousSteps)

    currentStepCard = [ renderCurrentStep viewInput state ]

    -- NOTE: Because the cards container is a flex element with a max width property, when there are more cards than
    --       can fit the view, the browser will try shrink them and remove any extra right margin/padding (not sure
    --       why this is only done to the right side). To avoid our cards getting shrinked, we add the flex-shrink-0
    --       property, and we add an empty `div` that occupies space (aka also cant be shrinked) to allow that the
    --       first and last card can be scrolled to the center
    paddingElement = [ div [ classNames [ "flex-shrink-0", "-ml-3", "w-carousel-padding-element", "h-full" ] ] [] ]
  in
    div
      [ classNames [ "flex", "flex-col", "items-center", "pt-3", "h-full", "w-screen", "relative" ] ]
      [ lifeCycleSlot "carousel-lifecycle" case _ of
          OnInit -> Just CarouselOpened
          OnFinalize -> Just CarouselClosed
      -- NOTE: The card is allowed to grow in an h-full container and the navigation buttons are absolute positioned
      --       because the cards x-scrolling can't coexist with a visible y-overflow. To avoid clipping the cards shadow
      --       we need the cards container to grow (hence the flex-grow).
      , div [ classNames [ "flex-grow", "w-full" ] ]
          [ div
              [ classNames [ "flex", "items-center", "overflow-x-scroll", "h-full", "scrollbar-width-none", "relative" ]
              , ref scrollContainerRef
              ]
              (paddingElement <> pastStepsCards <> currentStepCard <> paddingElement)
          ]
      , cardNavigationButtons state
      , div [ classNames [ "self-end", "pb-4", "pr-4", "font-bold" ] ] [ text $ statusIndicatorMessage state ]
      ]

statusIndicatorMessage :: State -> String
statusIndicatorMessage state =
  let
    userParties = state ^. _userParties

    participantsWithAction = Set.fromFoldable $ map fst $ state ^. _namedActions
  -- FIXME: as part of SCP-2551 add"Contract starting"
  in
    if Set.isEmpty (Set.intersection userParties participantsWithAction) then
      "Waiting for "
        <> if Set.size participantsWithAction > 1 then
            "multiple participants"
          else case Set.findMin participantsWithAction of
            Just (Role roleName) -> roleName
            Just (PK pubKey) -> take 4 pubKey
            Nothing -> " a timeout"
    else
      "Your turn..."

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
    div [ classNames [ "flex-grow" ] ]
      [ div [ classNames [ "flex", "items-center", "px-6", "py-2", "bg-white", "rounded", "shadow" ] ]
          $ leftButton
          <> [ icon Icon.Info [ "px-4", "invisible" ] ]
          <> rightButton
      ]

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
      [ "flex-grow", "text-center", "py-2", "text-sm", "font-semibold" ]
        <> case isActive of
            true -> [ "bg-white" ]
            false -> [ "bg-gray" ]

    contractCardCss =
      -- NOTE: The cards that are not selected gets scaled down to 77 percent of the original size. But when you scale down
      --       an element with CSS transform property, the parent still occupies the same layout dimensions as before,
      --       so the perceived margins are bigger than we'd want to. To solve this we add negative margin of 4
      --       to the "not selected" cards, a positive margin of 2 to the selected one
      -- Base classes
      [ "grid", "grid-rows-auto-1fr", "rounded", "overflow-hidden", "flex-shrink-0", "w-contract-card", "h-contract-card", "transform", "transition-transform", "duration-100", "ease-out", "mb-3" ]
        <> if (state ^. _selectedStep /= stepNumber) then
            -- Not selected card modifiers
            [ "-mx-4", "shadow-sm", "md:shadow", "scale-77" ]
          else
            -- Selected card modifiers
            [ "mx-2", "shadow-sm", "md:shadow-lg" ]
  in
    div [ classNames contractCardCss ]
      [ div [ classNames [ "flex", "select-none", "rounded-t", "overflow-hidden" ] ]
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

renderPastStep ::
  forall m.
  MonadAff m =>
  Input ->
  State ->
  Int ->
  PreviousStep ->
  ComponentHTML Action ChildSlots m
renderPastStep viewInput state stepNumber step =
  let
    currentTab = step ^. _tab

    renderBody Tasks { state: TransactionStep txInput } = renderPastStepTasksTab viewInput stepNumber state txInput step

    renderBody Tasks { state: TimeoutStep timeoutInfo } = renderTimeout viewInput state stepNumber timeoutInfo

    renderBody Balances { balances } = renderBalances stepNumber state balances

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
      , div [ classNames [ "overflow-y-auto", "bg-gray" ] ]
          [ renderBody currentTab step
          ]
      ]

type InputsByParty
  = { inputs :: Array S.Input, interval :: SlotInterval, party :: Party }

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
    NonEmptyArray { inputs :: Array S.Input, party :: Party } ->
    InputsByParty
  mergeInputsFromSameParty elements =
    foldr
      (\elem accu -> accu { inputs = elem.inputs <> accu.inputs })
      (NonEmptyArray.head elements # \{ party } -> { inputs: [], party, interval })
      elements

renderPastStepTasksTab ::
  forall m.
  MonadAff m =>
  Input ->
  Int ->
  State ->
  TransactionInput ->
  PreviousStep ->
  ComponentHTML Action ChildSlots m
renderPastStepTasksTab viewInput stepNumber state txInput step =
  let
    actionsByParticipant = groupTransactionInputByParticipant txInput

    resultingPayments = step ^. _resultingPayments
  in
    div [ classNames [ "px-4" ] ]
      $ if Array.length actionsByParticipant == 0 then
          -- TODO: See if we can reach this state and what text describes it better.
          [ div [ classNames [ "bg-white", "rounded", "shadow-sm", "my-4" ] ]
              [ text "An empty transaction was made to advance this step" ]
          ]
        else
          append
            (renderPartyPastActions viewInput state <$> actionsByParticipant)
            if length resultingPayments == 0 then
              []
            else
              [ renderPaymentSummary stepNumber state step ]

renderPaymentSummary :: forall p. Int -> State -> PreviousStep -> HTML p Action
renderPaymentSummary stepNumber state step =
  let
    expanded = step ^. _expandPayments

    -- TODO: This function is currently hard-coded to ADA, we should rethink how to deal with this
    --       when we support multiple tokens
    paymentToMovement (Payment from (Account to) money) = Transfer from to adaToken $ getAda money

    paymentToMovement (Payment from (Party to) money) = PayOut from to adaToken $ getAda money

    movements = paymentToMovement <$> step ^. _resultingPayments

    expandIcon = if expanded then Icon.ExpandLess else Icon.ExpandMore
  in
    div [ classNames [ "bg-white", "rounded", "shadow-sm", "my-4" ] ]
      ( append
          [ a
              [ classNames [ "px-4", "py-2", "flex", "justify-between", "items-center", "text-xs", "font-semibold", "select-none" ]
              , onClick_ $ ToggleExpandPayment stepNumber
              ]
              [ text "Payment summary"
              , icon_ expandIcon
              ]
          ]
          if not expanded then
            []
          else
            [ div [ classNames [ "px-4", "border-t", "border-gray" ] ]
                ( movements <#> \movement -> div [ classNames [ "py-4" ] ] [ renderMovement state movement ]
                )
            ]
      )

renderPartyPastActions ::
  forall m action.
  MonadAff m =>
  Input ->
  State ->
  InputsByParty ->
  ComponentHTML action ChildSlots m
renderPartyPastActions { tzOffset } state { inputs, interval, party } =
  let
    -- We don't know exactly when a transaction was executed, we have an interval. But
    -- the design asks for an exact date so we use the lower end of the interval so that
    -- we don't show a value in the future
    (SlotInterval intervalFrom _) = interval

    mTransactionDateTime = slotToDateTime intervalFrom

    transactionDate = maybe "-" (formatDate tzOffset) mTransactionDateTime

    transactionTime = maybe "-" (formatTime tzOffset) mTransactionDateTime

    renderPartyHeader =
      div [ classNames [ "flex", "justify-between", "items-center", "border-b", "border-gray", "px-3", "pb-4" ] ]
        [ renderParty [] state party
        , div [ classNames [ "flex", "flex-col", "items-end", "text-xxs", "font-semibold" ] ]
            [ span_ [ text transactionDate ]
            , span_ [ text $ transactionTime <> " (" <> humanizeOffset tzOffset <> ")" ]
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
      S.IDeposit intoAccountOf by token value -> renderMovement state (PayIn by intoAccountOf token value)
      S.IChoice (ChoiceId choiceIdKey _) chosenNum ->
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

renderTimeout :: forall p a. Input -> State -> Int -> TimeoutInfo -> HTML p a
renderTimeout { tzOffset } state stepNumber timeoutInfo =
  let
    mTimeoutDateTime = slotToDateTime timeoutInfo.slot

    timeoutDate = maybe "-" (formatDate tzOffset) mTimeoutDateTime

    timeoutTime = maybe "-" (formatTime tzOffset) mTimeoutDateTime

    header =
      div
        [ classNames [ "py-2", "px-3", "w-full", "flex", "justify-between" ] ]
        [ div [ classNames [ "flex", "items-center", "text-xs" ] ]
            [ icon Icon.Timer [ "mr-1" ]
            , span [ classNames [ "font-semibold" ] ] [ text "Timed out" ]
            ]
        , div [ classNames [ "flex", "flex-col", "items-end", "text-xxs", "font-semibold" ] ]
            [ span_ [ text timeoutDate ]
            , span_ [ text $ timeoutTime <> " (" <> humanizeOffset tzOffset <> ")" ]
            ]
        ]

    body =
      div [ classNames [ "py-2", "px-3", "border-t", "border-gray" ] ]
        $ renderMissingActions state timeoutInfo
  in
    div [ classNames [ "mt-4", "bg-white", "rounded", "shadow-sm", "mx-4", "flex", "flex-col", "items-center" ] ]
      [ header
      , body
      ]

renderMissingActions :: forall p a. State -> TimeoutInfo -> Array (HTML p a)
renderMissingActions _ { missedActions: [] } =
  [ div [ classNames [ "font-semibold", "text-xs", "leading-none" ] ] [ text "There were no tasks to complete at this step and the contract has timeouted as expected." ]
  ]

renderMissingActions state { missedActions } =
  append
    [ div [ classNames [ "font-semibold", "text-xs", "leading-none" ] ] [ text "The step timed out before the following actions could be made." ]
    ]
    (missedActions <#> uncurry (renderPartyMissingActions state))

renderPartyMissingActions :: forall p a. State -> Party -> Array NamedAction -> HTML p a
renderPartyMissingActions state party actions =
  let
    renderMissingAction (MakeChoice (ChoiceId name _) _ _) = span_ [ text "Make a choice for ", span [ classNames [ "font-semibold" ] ] [ text name ] ]

    renderMissingAction (MakeDeposit _ _ token value) = span [] [ text $ "Make a deposit of " <> humanizeValue token value ]

    renderMissingAction (MakeNotify _) = span [] [ text "awaiting observation" ]

    renderMissingAction _ = span [] [ text "invalid action" ]

    actionsSeparatedByOr =
      intercalate
        [ div [ classNames [ "font-semibold", "my-2", "text-xs" ] ] [ text "or" ]
        ]
        (Array.singleton <<< renderMissingAction <$> actions)
  in
    div [ classNames [ "border-l-2", "border-black", "pl-2", "mt-3" ] ]
      $ Array.cons (renderParty [ "mb-2" ] state party) actionsSeparatedByOr

renderCurrentStep :: forall m. MonadAff m => Input -> State -> ComponentHTML Action ChildSlots m
renderCurrentStep viewInput state =
  let
    stepNumber = currentStep state

    currentTab = state ^. _tab

    pendingTransaction = state ^. _pendingTransaction

    contractIsClosed = isContractClosed state

    mNextTimeout = state ^. (_executionState <<< _mNextTimeout)

    bodyBgColor = case currentTab of
      Tasks -> "bg-white"
      Balances -> "bg-gray"

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
              _, _ -> statusIndicator (Just Icon.Timer) (timeoutString viewInput.currentSlot state)
          ]
      , div
          [ classNames [ "overflow-y-auto", bodyBgColor ] ]
          [ currentStepActions stepNumber state ]
      ]

currentStepActions :: forall m. MonadAff m => Int -> State -> ComponentHTML Action ChildSlots m
currentStepActions stepNumber state =
  let
    currentTab = state ^. _tab

    pendingTransaction = state ^. _pendingTransaction
  in
    case currentTab, isContractClosed state, isJust pendingTransaction of
      Tasks, true, _ -> renderContractClose
      Tasks, _, true -> renderPendingStep
      Tasks, _, _ -> renderTasks state
      Balances, isClosed, _ ->
        let
          participants = state ^. _participants

          balancesAtStart = state ^. (_executionState <<< _semanticState <<< _accounts)

          atStart = expandBalances (Set.toUnfoldable $ Map.keys participants) [ adaToken ] balancesAtStart

          atEnd = if isClosed then Just atStart else Nothing
        in
          renderBalances stepNumber state { atStart, atEnd }

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

renderTasks :: forall p. State -> HTML p Action
renderTasks state =
  let
    namedActions = state ^. _namedActions
  in
    if length namedActions > 0 then
      div
        [ classNames [ "px-4", "pb-4" ] ]
        $ namedActions
        <#> uncurry (renderPartyTasks state)
    else
      noPossibleActions

noPossibleActions :: forall p a. HTML p a
noPossibleActions =
  let
    purpleDot extraCss = div [ classNames $ [ "rounded-full", "bg-lightpurple", "w-3", "h-3", "animate-grow" ] <> extraCss ] []
  in
    div
      [ classNames [ "p-4", "text-xs", "flex", "flex-col", "h-full" ] ]
      [ h4 [ classNames [ "font-semibold" ] ] [ text "Please wait…" ]
      , p [ classNames [ "mt-2" ] ] [ text "There are no tasks to complete at this step. The contract will progress automatically when the timeout passes." ]
      , div [ classNames [ "flex-grow", "flex", "justify-center", "items-center" ] ]
          [ purpleDot [ "mr-2" ]
          , purpleDot [ "animate-delay-150" ]
          , purpleDot [ "ml-2", "animate-delay-300" ]
          ]
      ]

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

renderMovement :: State -> Movement -> forall p a. HTML p a
renderMovement state movement =
  let
    fromParty = case movement of
      PayIn from _ _ _ -> renderParty [] state from
      Transfer from _ _ _ -> renderPartyAccount [] state from
      PayOut from _ _ _ -> renderPartyAccount [] state from

    toParty = case movement of
      PayIn _ to _ _ -> renderPartyAccount [] state to
      Transfer _ to _ _ -> renderPartyAccount [] state to
      PayOut _ to _ _ -> renderParty [] state to

    token = case movement of
      PayIn _ _ t _ -> t
      Transfer _ _ t _ -> t
      PayOut _ _ t _ -> t

    value = case movement of
      PayIn _ _ _ v -> v
      Transfer _ _ _ v -> v
      PayOut _ _ _ v -> v
  in
    div [ classNames [ "flex", "flex-col" ] ]
      [ fromParty
      , div [ classNames [ "flex", "justify-between", "items-center" ] ]
          [ icon Icon.South [ "text-purple", "text-xs", "ml-1" ]
          , span [ classNames [ "text-xs", "text-green" ] ] [ text $ humanizeValue token value ]
          ]
      , toParty
      ]

accountIndicator ::
  forall p a.
  { colorStyles :: Array String, otherStyles :: Array String, name :: String } ->
  HTML p a
accountIndicator { colorStyles, otherStyles, name } =
  div [ classNames $ [ "relative" ] <> otherStyles ]
    [ firstLetterInCircle { styles: colorStyles, name }
    , icon Icon.ReadMore [ "absolute", "text-xs", "-top-1", "right-0", "bg-white", "rounded-full" ]
    ]

firstLetterInCircle ::
  forall p a. { styles :: Array String, name :: String } -> HTML p a
firstLetterInCircle { styles, name } =
  div
    [ classNames
        $ [ "rounded-full"
          , "w-5"
          , "h-5"
          , "text-center"
          , "mr-1"
          , "font-semibold"
          ]
        <> styles
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
      [ firstLetterInCircle { styles: [ "bg-gradient-to-r", "from-purple", "to-lightpurple", "text-white" ], name: participantName }
      , div [ classNames [ "font-semibold" ] ]
          [ text $ if Set.member party userParties then participantName <> " (you)" else participantName
          ]
      ]

renderPartyAccount :: forall p a. Array String -> State -> Party -> HTML p a
renderPartyAccount styles state party =
  let
    participantName = participantWithNickname state party

    userParties = state ^. _userParties
  in
    div [ classNames $ [ "text-xs", "flex" ] <> styles ]
      [ accountIndicator { colorStyles: [ "bg-gradient-to-r", "from-purple", "to-lightpurple", "text-white" ], otherStyles: [], name: participantName }
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

renderBalances :: forall m a. MonadAff m => Int -> State -> StepBalance -> ComponentHTML a ChildSlots m
renderBalances stepNumber state stepBalance =
  let
    -- TODO: Right now we only have one type of Token (ada), but when we support multiple tokens we may want to group by
    --       participant and show the different tokens for each participant.
    -- NOTE: This transformation assumes that the balances at start and at end (if available) are
    --       expanded to all participants, because intersectionWith only produces values for duplicated
    --       keys. If a key is in one of the map but not the other, it won't be shown.
    accounts' :: Array (Tuple (Tuple Party Token) { atStart :: BigInteger, atEnd :: Maybe BigInteger })
    accounts' =
      Map.toUnfoldable
        $ maybe'
            (\_ -> stepBalance.atStart <#> \balance -> { atStart: balance, atEnd: Nothing })
            ( \balancesAtEnd ->
                Map.intersectionWith
                  (\atStart atEnd -> { atStart, atEnd: Just atEnd })
                  stepBalance.atStart
                  balancesAtEnd
            )
            stepBalance.atEnd
  in
    div [ classNames [ "text-xs" ] ]
      [ div
          [ classNames [ "bg-white", "py-1", "px-4", "mb-5", "flex", "items-center" ] ]
          [ icon Icon.ReadMore [ "mr-1" ]
          , span [ classNames [ "font-semibold" ] ] [ text "Balances of contract accounts" ]
          , hint [ "relative", "-top-1" ] ("balances-" <> show stepNumber) Auto
              -- FIXME: Revisit copy
              
              $ div_ [ text "This tab shows the amount of tokens that each role has in the contract account. A deposit is needed to get tokens from a wallet into the contract account, and a payment is needed to redeem tokens from the contract account into a user's wallet" ]
          ]
      , div [ classNames [ "px-4" ] ]
          ( accounts'
              <#> ( \((party /\ token) /\ balance) ->
                    let
                      participantName = participantWithNickname state party
                    in
                      div [ classNames [ "grid", "grid-cols-2", "gap-y-1", "py-3", "px-4", "mb-3", "shadow-sm", "bg-white", "rounded" ] ]
                        ( append
                            [ div [ classNames [ "flex" ] ]
                                [ accountIndicator
                                    { colorStyles:
                                        [ "bg-gradient-to-r", "from-purple", "to-lightpurple", "text-white", "mr-1" ]
                                    , otherStyles:
                                        [ "mr-1" ]
                                    , name: participantName
                                    }
                                , span [ classNames [ "font-semibold" ] ] [ text participantName ]
                                ]
                            , div [ classNames [ "font-semibold", "justify-self-end" ] ] [ text "Balance:" ]
                            , div [ classNames [] ] [ text "Step start:" ]
                            , div [ classNames [ "justify-self-end" ] ] [ text $ humanizeValue token balance.atStart ]
                            ]
                            $ maybe []
                                ( \balanceAtEnd ->
                                    [ div [ classNames [] ] [ text "Step end:" ]
                                    , div [ classNames [ "justify-self-end" ] ] [ text $ humanizeValue token balanceAtEnd ]
                                    ]
                                )
                                balance.atEnd
                        )
                )
          )
      ]

shortDescription :: forall p a. Boolean -> String -> HTML p a
shortDescription isActiveParticipant description =
  div [ classNames ([ "text-xs" ] <> applyWhen (not isActiveParticipant) [ "opacity-50" ]) ]
    [ span [ classNames [ "font-semibold" ] ] [ text "Short description: " ]
    , span_ $ markdownToHTML description
    ]

getParty :: S.Input -> Maybe Party
getParty (S.IDeposit _ p _ _) = Just p

getParty (S.IChoice (ChoiceId _ p) _) = Just p

getParty _ = Nothing
