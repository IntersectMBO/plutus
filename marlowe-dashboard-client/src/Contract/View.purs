module Contract.View
  ( contractPreviewCard
  , contractScreen
  ) where

import Prologue hiding (div)
import Component.Transfer.View (transfer)
import Component.Transfer.Types (Termini(..))
import Contacts.State (adaToken)
import Contract.Lenses (_executionState, _expandPayments, _metadata, _namedActions, _participants, _pendingTransaction, _previousSteps, _resultingPayments, _selectedStep, _stateMetadata, _stateNickname, _userParties)
import Contract.State (currentStep, isContractClosed, partyToParticipant, paymentToTransfer)
import Contract.Types (Action(..), Input, PreviousStep, PreviousStepState(..), StartedState, State(..), StepBalance, Tab(..), TimeoutInfo, scrollContainerRef)
import Css as Css
import Data.Array (foldr, fromFoldable, intercalate, length)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.BigInteger (BigInteger, fromString)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Lens ((^.))
import Data.Map (intersectionWith, keys, lookup, toUnfoldable) as Map
import Data.Maybe (isJust, maybe, maybe')
import Data.Set as Set
import Data.String (take, trim)
import Data.String.Extra (capitalize)
import Data.Tuple (uncurry)
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Css (applyWhen, classNames)
import Halogen.Extra (lifeCycleSlot, LifecycleEvent(..))
import Halogen.HTML (HTML, a, button, div, div_, h3, h4, h4_, input, p, p_, span, span_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (IProp, InputType(..), enabled, id_, placeholder, ref, type_, value)
import Hint.State (hint)
import Humanize (contractIcon, formatDate, formatTime, humanizeDuration, humanizeOffset, humanizeValue)
import MainFrame.Types (ChildSlots)
import Marlowe.Execution.Lenses (_contract, _mNextTimeout, _semanticState)
import Marlowe.Execution.State (expandBalances)
import Marlowe.Execution.Types (NamedAction(..))
import Marlowe.Extended.Metadata (_contractName, _contractType)
import Marlowe.PAB (transactionFee)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Contract(..), Party(..), Slot, SlotInterval(..), Token, TransactionInput(..), _accounts, getEncompassBound)
import Marlowe.Semantics (Input(..)) as S
import Marlowe.Slot (secondsDiff, slotToDateTime)
import Material.Icons (Icon(..)) as Icon
import Material.Icons (icon, icon_)
import Material.Progress.Circular as Progress
import Popper (Placement(..))
import Text.Markdown.TrimmedInline (markdownToHTML)
import Tooltip.State (tooltip)
import Tooltip.Types (ReferenceId(..))

-------------------------------------------------------------------------------
-- Top-level views
-------------------------------------------------------------------------------
-- This card shows a preview of the contract (intended to be used in the dashboard)
contractPreviewCard :: forall m. MonadAff m => Slot -> State -> ComponentHTML Action ChildSlots m
contractPreviewCard currentSlot state =
  let
    nickname = state ^. _stateNickname

    contractType = state ^. (_stateMetadata <<< _contractType)

    contractName = state ^. (_stateMetadata <<< _contractName)

    stepPanel = case state of
      Started started ->
        div
          [ classNames [ "px-4", "py-2" ] ]
          [ p
              [ classNames [ "text-xs", "font-semibold" ] ]
              [ text $ "Current step:" <> show (currentStep started + 1) ]
          , p
              [ classNames [ "font-semibold" ] ]
              [ text $ timeoutString currentSlot started ]
          ]
      Starting _ ->
        div
          [ classNames
              [ "px-4"
              , "py-2"
              , "flex"
              , "items-center"
              , "justify-between"
              ]
          ]
          [ p
              [ classNames [ "text-sm", "font-semibold" ] ]
              [ text $ "Starting contract…" ]
          , Progress.view Progress.defaultSpec
          ]
  in
    div
      [ classNames [ "shadow", "bg-white", "rounded", "divide-y", "divide-gray" ] ]
      [ div
          [ classNames [ "flex", "gap-2", "px-4", "py-2" ] ]
          [ div
              [ classNames [ "flex-1" ] ]
              [ h3
                  [ classNames [ "flex", "gap-2", "items-center" ] ]
                  [ contractIcon contractType
                  , text contractName
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
      , stepPanel
      , div
          [ classNames [ "h-dashboard-card-actions", "overflow-y-auto", "p-4" ] ]
          [ case state of
              Started started -> currentStepActions (currentStep started + 1) started
              Starting _ -> startingStepActions
          ]
      ]

contractScreen :: forall m. MonadAff m => Input -> State -> ComponentHTML Action ChildSlots m
contractScreen viewInput state =
  let
    cards = case state of
      Started started ->
        let
          pastStepsCards =
            mapWithIndex
              (renderPastStep viewInput started)
              (started ^. _previousSteps)

          currentStepCard = [ renderCurrentStep viewInput started ]

          cardForStep stepNumber
            | stepNumber == started.selectedStep = card [ "mx-2", "shadow-sm", "md:shadow-lg" ]
            | otherwise = card [ "-mx-4", "shadow-sm", "md:shadow", "scale-77" ]
        in
          mapWithIndex cardForStep $ pastStepsCards <> currentStepCard
      Starting _ ->
        [ card [ "shadow-sm", "md:shadow-lg" ]
            [ tabBar Tasks Nothing
            , cardBody []
                [ titleBar []
                    [ stepStatusText "Starting contract… " [ "flex-grow" ]
                    , Progress.view Progress.defaultSpec
                    ]
                , cardContent [] [ startingStepActions ]
                ]
            ]
        ]

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
              $ paddingElement
              <> cards
              <> paddingElement
          ]
      , cardNavigationButtons state
      , div [ classNames [ "self-end", "pb-4", "pr-4", "font-bold" ] ] [ text $ statusIndicatorMessage state ]
      ]

-------------------------------------------------------------------------------
-- UI components
-------------------------------------------------------------------------------
timeoutString :: Slot -> StartedState -> String
timeoutString currentSlot state =
  let
    mNextTimeout = state ^. (_executionState <<< _mNextTimeout)
  in
    maybe'
      (\_ -> if isContractClosed (Started state) then "Contract closed" else "Timed out")
      (\nextTimeout -> humanizeDuration $ secondsDiff nextTimeout currentSlot)
      mNextTimeout

statusIndicatorMessage :: State -> String
statusIndicatorMessage (Starting _) = "Starting contract…"

statusIndicatorMessage (Started state) =
  let
    userParties = state ^. _userParties

    participantsWithAction = Set.fromFoldable $ map fst $ state ^. _namedActions

    contract = state ^. (_executionState <<< _contract)
  in
    if contract == Close then
      "Contract completed"
    else
      if Set.isEmpty (Set.intersection userParties participantsWithAction) then
        "Waiting for "
          <> if Set.size participantsWithAction > 1 then
              "multiple participants"
            else case Set.findMin participantsWithAction of
              Just (Role roleName) -> roleName
              Just (PK pubKey) -> take 4 pubKey
              Nothing -> " a timeout"
      else
        "Your turn…"

cardNavigationButtons :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
cardNavigationButtons (Starting _) = div [] []

cardNavigationButtons (Started state) =
  let
    lastStep = currentStep state

    selectedStep = state ^. _selectedStep

    contractIsClosed = isContractClosed (Started state)

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

renderPastStep ::
  forall m.
  MonadAff m =>
  Input ->
  StartedState ->
  Int ->
  PreviousStep ->
  Array (ComponentHTML Action ChildSlots m)
renderPastStep viewInput state stepNumber step =
  [ tabBar step.tab $ Just (SelectTab stepNumber)
  , cardBody []
      $ [ titleBar []
            [ numberedStepTitle stepNumber
            , case step.state of
                TimeoutStep _ ->
                  stepStatus []
                    [ stepStatusText "Timed out" []
                    , icon Icon.Timer []
                    ]
                TransactionStep _ ->
                  stepStatus []
                    [ icon Icon.Done [ "text-green" ]
                    , stepStatusText "Completed" [ "text-green" ]
                    ]
            ]
        , case step.tab, step of
            Tasks, { state: TransactionStep txInput } -> cardContent [ "p-4" ] [ renderPastStepTasksTab viewInput stepNumber state txInput step ]
            Tasks, { state: TimeoutStep timeoutInfo } -> cardContent [ "p-4" ] [ renderTimeout viewInput state stepNumber timeoutInfo ]
            Balances, { balances } -> cardContent [] [ renderBalances stepNumber state balances ]
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
  StartedState ->
  TransactionInput ->
  PreviousStep ->
  ComponentHTML Action ChildSlots m
renderPastStepTasksTab viewInput stepNumber state txInput step =
  let
    actionsByParticipant = groupTransactionInputByParticipant txInput

    resultingPayments = step ^. _resultingPayments
  in
    div [ classNames [ "space-y-4" ] ]
      if Array.length actionsByParticipant == 0 then
        -- TODO: See if we can reach this state and what text describes it better.
        [ div [ classNames [ "bg-white", "rounded", "shadow-sm" ] ]
            [ text "An empty transaction was made to advance this step" ]
        ]
      else
        append
          (renderPartyPastActions viewInput state <$> actionsByParticipant)
          if length resultingPayments == 0 then
            []
          else
            [ renderPaymentSummary stepNumber state step ]

renderPaymentSummary :: forall p. Int -> StartedState -> PreviousStep -> HTML p Action
renderPaymentSummary stepNumber state step =
  let
    expanded = step ^. _expandPayments

    transfers = paymentToTransfer state <$> step ^. _resultingPayments

    expandIcon = if expanded then Icon.ExpandLess else Icon.ExpandMore
  in
    div [ classNames [ "bg-white", "rounded", "shadow-sm", "divide-y", "divide-gray" ] ]
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
            [ div [ classNames [ "px-4" ] ]
                $ div [ classNames [ "py-4" ] ]
                <<< pure
                <<< transfer
                <$> transfers
            ]
      )

renderPartyPastActions ::
  forall m action.
  MonadAff m =>
  Input ->
  StartedState ->
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
      div [ classNames [ "flex", "justify-between", "items-center", "p-4" ] ]
        [ renderParty state party
        , div [ classNames [ "flex", "flex-col", "items-end", "text-xxs", "font-semibold" ] ]
            [ span_ [ text transactionDate ]
            , span_ [ text $ transactionTime <> " (" <> humanizeOffset tzOffset <> ")" ]
            ]
        ]

    renderFeesSummary =
      div [ classNames [ "p-4", "flex", "items-center", "text-xs", "gap-1" ] ]
        [ icon Icon.Language [ "text-lightpurple", "text-lg" ]
        , span [ classNames [ "font-semibold" ] ]
            [ text "Total fees:"
            ]
        , span [ classNames [ "flex-grow", "text-right" ] ] [ text $ humanizeValue adaToken transactionFee ]
        ]

    renderActionsBody =
      div [ classNames [ "p-4", "space-y-4" ] ]
        (map renderPastAction inputs)

    renderPastAction = case _ of
      S.IDeposit recipient sender token quantity ->
        transfer
          { sender: partyToParticipant state sender
          , recipient: partyToParticipant state recipient
          , token
          , quantity
          , termini: WalletToAccount sender recipient
          }
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
    div [ classNames [ "bg-white", "rounded", "shadow-sm", "divide-y", "divide-gray" ] ]
      [ renderPartyHeader
      , renderActionsBody
      , renderFeesSummary
      ]

renderTimeout :: forall p a. Input -> StartedState -> Int -> TimeoutInfo -> HTML p a
renderTimeout { tzOffset } state stepNumber timeoutInfo =
  let
    mTimeoutDateTime = slotToDateTime timeoutInfo.slot

    timeoutDate = maybe "-" (formatDate tzOffset) mTimeoutDateTime

    timeoutTime = maybe "-" (formatTime tzOffset) mTimeoutDateTime

    header =
      div
        [ classNames [ "p-2", "gap-2", "w-full", "flex", "justify-between" ] ]
        [ div [ classNames [ "flex", "items-center", "text-xs", "gap-1" ] ]
            [ icon_ Icon.Timer
            , span [ classNames [ "font-semibold" ] ] [ text "Timed out" ]
            ]
        , div [ classNames [ "flex", "flex-col", "items-end", "text-xxs", "font-semibold" ] ]
            [ span_ [ text timeoutDate ]
            , span_ [ text $ timeoutTime <> " (" <> humanizeOffset tzOffset <> ")" ]
            ]
        ]

    body =
      div [ classNames [ "p-2", "space-y-2" ] ]
        $ renderMissingActions state timeoutInfo
  in
    div [ classNames [ "divide-y", "divide-gray", "bg-white", "rounded", "shadow-sm", "flex", "flex-col", "items-center" ] ]
      [ header
      , body
      ]

renderMissingActions :: forall p a. StartedState -> TimeoutInfo -> Array (HTML p a)
renderMissingActions _ { missedActions: [] } =
  [ div [ classNames [ "font-semibold", "text-xs", "leading-none" ] ] [ text "There were no tasks to complete at this step and the contract has timeouted as expected." ]
  ]

renderMissingActions state { missedActions } =
  append
    [ div [ classNames [ "font-semibold", "text-xs", "leading-none" ] ] [ text "The step timed out before the following actions could be made." ]
    ]
    (missedActions <#> uncurry (renderPartyMissingActions state))

renderPartyMissingActions :: forall p a. StartedState -> Party -> Array NamedAction -> HTML p a
renderPartyMissingActions state party actions =
  let
    renderMissingAction (MakeChoice (ChoiceId name _) _ _) = span_ [ text "Make a choice for ", span [ classNames [ "font-semibold" ] ] [ text name ] ]

    renderMissingAction (MakeDeposit _ _ token value) = span [] [ text $ "Make a deposit of " <> humanizeValue token value ]

    renderMissingAction (MakeNotify _) = span [] [ text "awaiting observation" ]

    renderMissingAction _ = span [] [ text "invalid action" ]

    actionsSeparatedByOr =
      intercalate
        [ div [ classNames [ "font-semibold", "text-xs" ] ] [ text "or" ]
        ]
        (Array.singleton <<< renderMissingAction <$> actions)
  in
    div [ classNames [ "border-l-2", "border-black", "pl-2", "space-y-2" ] ]
      $ Array.cons (renderParty state party) actionsSeparatedByOr

renderCurrentStep ::
  forall m.
  MonadAff m =>
  Input ->
  StartedState ->
  Array (ComponentHTML Action ChildSlots m)
renderCurrentStep viewInput state =
  let
    stepNumber = currentStep state

    pendingTransaction = state ^. _pendingTransaction

    contractIsClosed = isContractClosed (Started state)

    mNextTimeout = state ^. (_executionState <<< _mNextTimeout)
  in
    [ tabBar state.tab $ Just (SelectTab stepNumber)
    , cardBody []
        $ [ titleBar []
              [ numberedStepTitle stepNumber
              , stepStatus []
                  $ case contractIsClosed, isJust pendingTransaction of
                      true, _ -> [ stepStatusText "Contract closed" [] ]
                      _, true -> [ stepStatusText "Awaiting confirmation" [] ]
                      _, _ ->
                        [ stepStatusText (timeoutString viewInput.currentSlot state) []
                        , icon Icon.Timer []
                        ]
              ]
          , case state.tab of
              Tasks -> cardContent [ "bg-wite", "p-4" ] [ currentStepActions stepNumber state ]
              Balances ->
                let
                  participants = state ^. _participants

                  balancesAtStart = state ^. (_executionState <<< _semanticState <<< _accounts)

                  atStart = expandBalances (Set.toUnfoldable $ Map.keys participants) [ adaToken ] balancesAtStart

                  atEnd = if isJust state.pendingTransaction then Just atStart else Nothing
                in
                  cardContent [ "bg-gray" ] [ renderBalances stepNumber state { atStart, atEnd } ]
          ]
    ]

startingStepActions :: forall p a. HTML p a
startingStepActions =
  div [ classNames [ "space-y-6" ] ]
    [ placeholderAccount
    , placeholderContent
    ]
  where
  placeholderAccount =
    div [ classNames [ "flex", "items-center", "gap-1" ] ]
      [ placeholderAvatar
      , placeholderName
      ]

  placeholderAvatar = div [ classNames [ "bg-gray", "rounded-full", "w-5", "h-5" ] ] []

  placeholderName = div [ classNames [ "bg-gray", "rounded-sm", "w-1/2", "h-6" ] ] []

  placeholderContent = div [ classNames [ "bg-gray", "rounded-full", "w-full", "h-12" ] ] []

currentStepActions :: forall m. MonadAff m => Int -> StartedState -> ComponentHTML Action ChildSlots m
currentStepActions stepNumber state = case isContractClosed (Started state), isJust state.pendingTransaction, state.namedActions of
  true, _, _ ->
    div [ classNames [ "h-full", "flex", "flex-col", "justify-center", "items-center" ] ]
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
  _, true, _ ->
    -- FIXME: when we have a design for this, we can include more information (probably making this look more like
    -- the past step card)
    div_
      [ text "Your transaction has been submitted. You will be notified when confirmation is received." ]
  _, _, [] ->
    let
      purpleDot extraCss = div [ classNames $ [ "rounded-full", "bg-lightpurple", "w-3", "h-3", "animate-grow" ] <> extraCss ] []
    in
      div
        [ classNames [ "text-xs", "flex", "flex-col", "h-full", "gap-2" ] ]
        [ h4 [ classNames [ "font-semibold" ] ] [ text "Please wait…" ]
        , p_
            [ text "There are no tasks to complete at this step. The contract will progress automatically when the timeout passes." ]
        , div [ classNames [ "flex-grow", "flex", "justify-center", "items-center", "gap-2" ] ]
            [ purpleDot []
            , purpleDot [ "animate-delay-150" ]
            , purpleDot [ "animate-delay-300" ]
            ]
        ]
  _, _, namedActions ->
    div
      [ classNames [ "space-y-4" ] ]
      $ uncurry (renderPartyTasks state)
      <$> namedActions

participantWithNickname :: StartedState -> Party -> String
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
          , "font-semibold"
          ]
        <> styles
    ]
    [ text $ take 1 name ]

-- TODO: In zeplin all participants have a different color. We need to decide how are we going to assing
--       colors to users. For now they all have purple
renderParty :: forall p a. StartedState -> Party -> HTML p a
renderParty state party =
  let
    participantName = participantWithNickname state party

    userParties = state ^. _userParties
  in
    div [ classNames $ [ "text-xs", "flex", "gap-1" ] ]
      [ firstLetterInCircle { styles: [ "bg-gradient-to-r", "from-purple", "to-lightpurple", "text-white" ], name: participantName }
      , div [ classNames [ "font-semibold" ] ]
          [ text $ if Set.member party userParties then participantName <> " (you)" else participantName
          ]
      ]

renderPartyTasks :: forall p. StartedState -> Party -> Array NamedAction -> HTML p Action
renderPartyTasks state party actions =
  let
    actionsSeparatedByOr =
      intercalate
        [ div [ classNames [ "font-semibold", "text-center", "text-xs" ] ] [ text "OR" ]
        ]
        (Array.singleton <<< renderAction state party <$> actions)
  in
    div [ classNames [ "space-y-2" ] ]
      ([ renderParty state party ] <> actionsSeparatedByOr)

-- FIXME: This was added to allow anybody being able to do any actions for debug purposes...
--        Remove once the PAB is connected
debugMode :: Boolean
debugMode = false

-- The Party parameter represents who is taking the action
renderAction :: forall p. StartedState -> Party -> NamedAction -> HTML p Action
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
    div [ classNames [ "space-y-2" ] ]
      [ shortDescription isActiveParticipant description
      , button
          [ classNames $ Css.button <> Css.withAnimation <> [ "flex", "justify-between", "w-full" ]
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
        [ classNames $ Css.button <> Css.withAnimation <> [ "w-full" ]
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
    div [ classNames [ "space-y-2" ] ]
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
    div [ classNames [ "space-y-2" ] ]
      -- FIXME: revisit the text
      [ shortDescription isActiveParticipant "The contract is still open and needs to be manually closed by any participant for the remainder of the balances to be distributed (charges may apply)"
      , button
          [ classNames $ Css.button <> Css.withAnimation <> [ "w-full" ]
              <> if isActiveParticipant || debugMode then
                  Css.bgBlueGradient <> Css.withShadow
                else
                  [ "text-black", "cursor-default" ]
          , enabled $ isActiveParticipant || debugMode
          , onClick_ $ AskConfirmation CloseContract
          ]
          [ text "Close contract" ]
      ]

renderBalances :: forall m a. MonadAff m => Int -> StartedState -> StepBalance -> ComponentHTML a ChildSlots m
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
    div [ classNames [ "text-xs", "space-y-4" ] ]
      [ div
          [ classNames [ "bg-white", "py-1", "px-4", "gap-1", "flex", "items-center" ] ]
          [ icon_ Icon.ReadMore
          , span [ classNames [ "font-semibold" ] ] [ text "Balances of contract accounts" ]
          , hint [ "relative", "-top-1" ] ("balances-" <> show stepNumber) Auto
              -- FIXME: Revisit copy
              
              $ div_ [ text "This tab shows the amount of tokens that each role has in the contract account. A deposit is needed to get tokens from a wallet into the contract account, and a payment is needed to redeem tokens from the contract account into a user's wallet" ]
          ]
      , div [ classNames [ "px-4", "space-y-3" ] ]
          ( accounts'
              <#> ( \((party /\ token) /\ balance) ->
                    let
                      participantName = participantWithNickname state party
                    in
                      div [ classNames [ "grid", "grid-cols-2", "gap-y-1", "py-3", "px-4", "shadow-sm", "bg-white", "rounded" ] ]
                        ( append
                            [ div [ classNames [ "flex", "gap-1" ] ]
                                [ accountIndicator
                                    { colorStyles:
                                        [ "bg-gradient-to-r", "from-purple", "to-lightpurple", "text-white" ]
                                    , otherStyles:
                                        []
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

-------------------------------------------------------------------------------
-- UI Layout helpers
-------------------------------------------------------------------------------
withBaseCss ::
  forall i r p action.
  (Array (IProp ( class :: String | r ) i) -> Array (HTML p action) -> HTML p action) ->
  Array String ->
  Array String ->
  Array (HTML p action) ->
  HTML p action
withBaseCss el baseCss css children = el [ classNames $ baseCss <> css ] children

card :: forall p action. Array String -> Array (HTML p action) -> HTML p action
card =
  div
    `withBaseCss`
      [ "grid"
      , "grid-rows-auto-1fr"
      , "rounded"
      , "overflow-hidden"
      , "flex-shrink-0"
      , "w-contract-card"
      , "h-contract-card"
      , "transform"
      , "transition-transform"
      , "duration-100"
      , "ease-out"
      ]

tabBar :: forall p action. Tab -> Maybe (Tab -> action) -> HTML p action
tabBar current onClick =
  let
    css = [ "flex", "select-none", "rounded-t", "overflow-hidden" ]

    tab tab' =
      let
        bgColor
          | current == tab' = "bg-white"
          | otherwise = "bg-gray"

        title = case tab' of
          Tasks -> "Tasks"
          Balances -> "Balances"
      in
        a
          ( [ classNames
                [ "flex-grow"
                , "text-center"
                , "py-2"
                , "text-sm"
                , "font-semibold"
                , bgColor
                ]
            ]
              <> fromFoldable (onClick_ <$> (onClick <*> pure tab'))
          )
          [ span_ $ [ text title ] ]
  in
    div [ classNames css ] [ tab Tasks, tab Balances ]

cardBody :: forall p action. Array String -> Array (HTML p action) -> HTML p action
cardBody = div `withBaseCss` [ "bg-white", "grid", "grid-rows-auto-1fr", "divide-y", "divide-lightgray" ]

titleBar :: forall p action. Array String -> Array (HTML p action) -> HTML p action
titleBar = div `withBaseCss` [ "py-2.5", "px-4", "flex", "items-center" ]

cardContent :: forall p action. Array String -> Array (HTML p action) -> HTML p action
cardContent = div `withBaseCss` [ "overflow-y-auto" ]

numberedStepTitle :: forall p action. Int -> HTML p action
numberedStepTitle stepNumber = stepTitle $ "Step " <> show (stepNumber + 1)

stepTitle :: forall p action. String -> HTML p action
stepTitle s =
  span
    [ classNames [ "text-xl", "font-semibold", "flex-grow" ] ]
    [ text s ]

stepStatus :: forall p action. Array String -> Array (HTML p action) -> HTML p action
stepStatus = div `withBaseCss` [ "h-10", "flex", "items-center", "gap-2" ]

stepStatusText :: forall p action. String -> Array String -> HTML p action
stepStatusText message css =
  span
    [ classNames $ [ "select-none", "font-semibold" ] <> css ]
    [ text message ]
