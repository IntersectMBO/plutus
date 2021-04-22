module Contract.State
  ( handleQuery
  , handleAction
  , mkInitialState
  , instantiateExtendedContract
  , dummyState
  , currentStep
  , isContractClosed
  , applyTx
  , applyTimeout
  ) where

import Prelude
import Capability.Toast (class Toast, addToast)
import Contract.Lenses (_contractInstanceId, _executionState, _namedActions, _previousSteps, _selectedStep, _tab)
import Contract.Types (Action(..), PreviousStep, PreviousStepState(..), Query(..), State, Tab(..), scrollContainerRef)
import Control.Monad.Reader (class MonadAsk, asks)
import Data.Array as Array
import Data.Foldable (for_)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Lens (assign, modifying, over, to, toArrayOf, traversed, use, view, (^.))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Ord (abs)
import Data.RawJson (RawJson(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Data.UUID (emptyUUID)
import Data.Unfoldable as Unfoldable
import Effect (Effect)
import Effect.Aff.AVar as AVar
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Effect.Exception.Unsafe (unsafeThrow)
import Env (Env)
import Foreign.Generic (encode)
import Foreign.JSON (unsafeStringify)
import Halogen (HalogenM, SubscriptionId, getHTMLElementRef, gets, liftEffect, modify_, subscribe, subscribe', unsubscribe)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Execution (NamedAction(..), PreviousState, _currentContract, _currentState, _pendingTimeouts, _previousState, expandBalances, extractNamedActions, initExecution, isClosed, mkTx, nextState, timeoutState)
import Marlowe.Extended (TemplateContent, fillTemplate, resolveRelativeTimes, toCore)
import Marlowe.Extended as Extended
import Marlowe.Extended.Metadata (MetaData, emptyContractMetadata)
import Marlowe.Semantics (Contract(..), Input(..), Slot, SlotInterval(..), Token(..), TransactionInput(..))
import Marlowe.Semantics as Semantic
import Marlowe.Slot (currentSlot)
import Toast.Types (successToast)
import Types (ContractInstanceId(..))
import WalletData.Types (WalletNickname)
import Web.DOM.Element (getElementsByClassName)
import Web.DOM.HTMLCollection as HTMLCollection
import Web.DOM.IntersectionObserver (disconnect, intersectionObserver, observe)
import Web.Dom.ElementExtra (Alignment(..), ScrollBehavior(..), debouncedOnScroll, scrollIntoView, throttledOnScroll)
import Web.HTML (HTMLElement)
import Web.HTML.HTMLElement (getBoundingClientRect, offsetLeft)
import Web.HTML.HTMLElement as HTMLElement

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState emptyContractInstanceId zero emptyContractMetadata mempty Nothing Close
  where
  emptyContractInstanceId = ContractInstanceId emptyUUID

currentStep :: State -> Int
currentStep = Array.length <<< view _previousSteps

toInput :: NamedAction -> Maybe Input
toInput (MakeDeposit accountId party token value) = Just $ IDeposit accountId party token value

toInput (MakeChoice choiceId _ (Just chosenNum)) = Just $ IChoice choiceId chosenNum

-- WARNING:
--       This is possible in the types but should never happen in runtime. And I prefer to explicitly throw
--       an error if it happens than silently omit it by returning Nothing (which in case of Input, it has
--       the semantics of an empty transaction).
--       The reason we use Maybe in the chosenNum is that we use the same NamedAction data type
--       for triggering the action and to display to the user what choice did he/she made. And we need
--       to represent that initialy no choice is made, and eventually you can type an option and delete it.
--       Another way to do this would be to duplicate the NamedAction data type with just that difference, which
--       seems like an overkill.
toInput (MakeChoice _ _ Nothing) = unsafeThrow "A choice action has been triggered"

toInput (MakeNotify _) = Just $ INotify

toInput _ = Nothing

isContractClosed :: State -> Boolean
isContractClosed state = isClosed $ state ^. _executionState

instantiateExtendedContract ::
  ContractInstanceId ->
  Slot ->
  Extended.Contract ->
  TemplateContent ->
  MetaData ->
  Map Semantic.Party (Maybe WalletNickname) ->
  Maybe Semantic.Party ->
  Maybe State
instantiateExtendedContract contractInstanceId currentSlot extendedContract templateContent metadata participants mActiveUserParty =
  let
    relativeContract = resolveRelativeTimes currentSlot extendedContract

    mContract = toCore $ fillTemplate templateContent relativeContract
  in
    mContract
      <#> mkInitialState contractInstanceId currentSlot metadata participants mActiveUserParty

mkInitialState ::
  ContractInstanceId ->
  Slot ->
  MetaData ->
  Map Semantic.Party (Maybe WalletNickname) ->
  Maybe Semantic.Party ->
  Contract ->
  State
mkInitialState contractInstanceId slot metadata participants mActiveUserParty contract =
  let
    executionState = initExecution slot contract
  in
    { tab: Tasks
    , executionState
    , previousSteps: mempty
    , contractInstanceId
    , selectedStep: 0
    , metadata
    , participants
    , mActiveUserParty
    , namedActions: extractNamedActions slot executionState
    }

handleQuery :: forall a m. MonadEffect m => Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ApplyTx tx next) = do
  slot <- liftEffect $ currentSlot
  modify_ $ applyTx slot tx
  pure $ Just next

transactionsToStep :: State -> PreviousState -> PreviousStep
transactionsToStep { participants } { txInput, state } =
  let
    TransactionInput { interval: SlotInterval minSlot maxSlot, inputs } = txInput

    -- TODO: When we add support for multiple tokens we should extract the possible tokens from the
    --       contract, store it in ContractState and pass them here.
    balances = expandBalances (Set.toUnfoldable $ Map.keys participants) [ Token "" "" ] state

    stepState =
      -- For the moment the only way to get an empty transaction is if there was a timeout,
      -- but later on there could be other reasons to move a contract forward, and we should
      -- compare with the contract to see the reason.
      if inputs == mempty then
        TimeoutStep minSlot
      else
        TransactionStep txInput
  in
    { balances
    , state: stepState
    }

timeoutToStep :: State -> Slot -> PreviousStep
timeoutToStep { participants, executionState } slot =
  let
    currentContractState = executionState ^. _currentState

    balances = expandBalances (Set.toUnfoldable $ Map.keys participants) [ Token "" "" ] currentContractState
  in
    { balances
    , state: TimeoutStep slot
    }

regenerateStepCards :: Slot -> State -> State
regenerateStepCards currentSlot state =
  let
    confirmedSteps :: Array PreviousStep
    confirmedSteps = toArrayOf (_executionState <<< _previousState <<< traversed <<< to (transactionsToStep state)) state

    pendingTimeoutSteps :: Array PreviousStep
    pendingTimeoutSteps = toArrayOf (_executionState <<< _pendingTimeouts <<< traversed <<< to (timeoutToStep state)) state

    previousSteps = confirmedSteps <> pendingTimeoutSteps

    namedActions = extractNamedActions currentSlot (state ^. _executionState)
  in
    state { previousSteps = previousSteps, namedActions = namedActions }

selectLastStep :: State -> State
selectLastStep state@{ previousSteps } = state { selectedStep = Array.length previousSteps }

applyTx :: Slot -> TransactionInput -> State -> State
applyTx currentSlot txInput state =
  let
    updateExecutionState = over _executionState (\s -> nextState s txInput)
  in
    state
      # updateExecutionState
      # regenerateStepCards currentSlot
      # selectLastStep

applyTimeout :: Slot -> State -> State
applyTimeout currentSlot state =
  let
    updateExecutionState = over _executionState (timeoutState currentSlot)
  in
    state
      # updateExecutionState
      # regenerateStepCards currentSlot
      # selectLastStep

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Toast m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (ConfirmAction namedAction) = do
  currentExeState <- use _executionState
  contractId <- use _contractInstanceId
  slot <- liftEffect currentSlot
  let
    input = toInput namedAction

    txInput = mkTx slot (currentExeState ^. _currentContract) (Unfoldable.fromMaybe input)

    json = RawJson <<< unsafeStringify <<< encode $ input
  -- TODO: currently we just ignore errors but we probably want to do something better in the future
  -- FIXME: send data to BE
  -- void $ mapEnvReaderT _.ajaxSettings $ runExceptT $ postApiContractByContractinstanceidEndpointByEndpointname json contractId "apply-inputs"
  modify_ $ applyTx slot txInput
  stepNumber <- gets currentStep
  handleAction $ MoveToStep stepNumber
  addToast $ successToast "Payment received, step completed"

-- raise (SendWebSocketMessage (ServerMsg true)) -- FIXME: send txInput to the server to apply to the on-chain contract
handleAction (ChangeChoice choiceId chosenNum) = modifying _namedActions (map changeChoice)
  where
  changeChoice (MakeChoice choiceId' bounds _)
    | choiceId == choiceId' = MakeChoice choiceId bounds chosenNum

  changeChoice namedAction = namedAction

handleAction (SelectTab tab) = assign _tab tab

handleAction (AskConfirmation action) = pure unit -- Managed by Play.State

handleAction CancelConfirmation = pure unit -- Managed by Play.State

handleAction (SelectStep stepNumber) = assign _selectedStep stepNumber

handleAction (MoveToStep stepNumber) = do
  -- The MoveToStep action is called when a new step is added (either via an apply transaction or
  -- a timeout). We unsubscribe and resubscribe to update the tracked elements.
  unsubscribeFromSelectCenteredStep
  subscribeToSelectCenteredStep
  mElement <- getHTMLElementRef scrollContainerRef
  for_ mElement $ liftEffect <<< scrollStepToCenter Smooth stepNumber

handleAction CarouselOpened = do
  selectedStep <- use _selectedStep
  mElement <- getHTMLElementRef scrollContainerRef
  for_ mElement \elm -> do
    -- When the carousel is opened we want to assure that the selected step is
    -- in the center without any animation
    liftEffect $ scrollStepToCenter Auto selectedStep elm
    subscribe' $ carouselCloseEventSource elm
    subscribeToSelectCenteredStep

handleAction CarouselClosed = unsubscribeFromSelectCenteredStep

-- NOTE: In the first version of the selectCenteredStep feature the subscriptionId was stored in the
--       Contract.State as a Maybe SubscriptionId. But when calling subscribe/unsubscribe multiple
--       times in a small period of time there was a concurrency issue and multiple subscriptions
--       were active at the same time, which caused scroll issues.
unsubscribeFromSelectCenteredStep ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  HalogenM State Action ChildSlots Msg m Unit
unsubscribeFromSelectCenteredStep = do
  mutex <- asks _.contractStepCarouselSubscription
  mSubscription <- liftAff $ AVar.tryTake mutex
  for_ mSubscription unsubscribe

subscribeToSelectCenteredStep ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  HalogenM State Action ChildSlots Msg m Unit
subscribeToSelectCenteredStep = do
  mElement <- getHTMLElementRef scrollContainerRef
  for_ mElement \elm -> do
    subscription <- subscribe $ selectCenteredStepEventSource elm
    -- We try to update the subscription without blocking, and if we cant (because another
    -- subscription is already present, then we clean this one, so only one subscription can
    -- be active at a time)
    mutex <- asks _.contractStepCarouselSubscription
    mutexUpdated <- liftAff $ AVar.tryPut subscription mutex
    when (not mutexUpdated) $ unsubscribe subscription

scrollStepToCenter ::
  ScrollBehavior ->
  Int ->
  HTMLElement ->
  Effect Unit
scrollStepToCenter behavior stepNumber parentElement = do
  let
    getStepElemets = HTMLCollection.toArray =<< getElementsByClassName "w-contract-card" (HTMLElement.toElement parentElement)
  mStepElement <- flip Array.index stepNumber <$> getStepElemets
  for_ mStepElement $ scrollIntoView { block: Center, inline: Center, behavior }

-- Because this is a subcomponent, we don't have a `Finalize` event that we can use, so we add a self contained
-- subscription (a.k.a. it closes itself) that detects when the modal is no longer visible (not intersecting with the
-- viewport)
carouselCloseEventSource ::
  forall m.
  MonadAff m =>
  HTMLElement ->
  SubscriptionId ->
  EventSource m Action
carouselCloseEventSource parentElement _ =
  EventSource.effectEventSource \emitter -> do
    observer <-
      intersectionObserver {} \entries _ ->
        for_ (Array.head entries) \entry ->
          when (not entry.isIntersecting) do
            EventSource.emit emitter CarouselClosed
            EventSource.close emitter
    observe (HTMLElement.toElement parentElement) observer
    pure $ EventSource.Finalizer $ disconnect observer

-- This EventSource is responsible for selecting the step closest to the center of the scroll container
-- when scrolling
selectCenteredStepEventSource ::
  forall m.
  MonadAff m =>
  HTMLElement ->
  EventSource m Action
selectCenteredStepEventSource scrollContainer =
  EventSource.effectEventSource \emitter -> do
    -- Calculate where the left coordinate of the center step should be
    -- (relative to the visible part of the scroll container)
    parentWidth <- _.width <$> getBoundingClientRect scrollContainer
    let
      stepCardWidth = 264.0

      intendedLeft = parentWidth / 2.0 - stepCardWidth / 2.0
    -- Calculate the left coordinate of all cards relative to the scroll container (which needs to have a
    -- display: relative property)
    stepElements <- HTMLCollection.toArray =<< getElementsByClassName "w-contract-card" (HTMLElement.toElement scrollContainer)
    stepLeftOffsets <- traverse offsetLeft $ Array.mapMaybe HTMLElement.fromElement stepElements
    let
      calculateClosestStep scrollPos =
        _.index
          $ foldlWithIndex
              ( \index accu stepLeftOffset ->
                  let
                    diff = abs $ stepLeftOffset - (scrollPos.left + intendedLeft)
                  in
                    if diff < accu.diff then { diff, index } else accu
              )
              { index: 0, diff: top }
              stepLeftOffsets
    -- We use two different scroll listeners:
    -- * The first one is responsible for actually selecting the step closest to the center. It is throttled,
    --   which means that it will be called at most once in every `window of time`. We do this because the
    --   scroll event dispatch several events per scroll action and the callback is handled in the main thread
    --   so if we do a heavy computation, the browser can lag.
    unsubscribeSelectEventListener <-
      throttledOnScroll
        50.0
        (HTMLElement.toElement scrollContainer)
        (calculateClosestStep >>> \index -> EventSource.emit emitter $ SelectStep index)
    -- * The second one is responsible for snapping the card to the center position. Initially this was
    --   handled by CSS using the `scroll-snap-type` and `scroll-snap-align` properties. But I found a bug
    --   in chrome when those properties were used at the same time of a `smooth` scrollTo, so I ended up
    --   doing manual snapping. The event is debounced, which means that it will be called just once after
    --   X time with no scroll events.
    unsubscribeSnapEventListener <-
      debouncedOnScroll
        150.0
        (HTMLElement.toElement scrollContainer) \scrollPos -> do
        let
          index = calculateClosestStep scrollPos
        scrollStepToCenter Smooth index scrollContainer
        EventSource.emit emitter $ SelectStep index
    -- (calculateClosestStep >>> \index -> scrollStepToCenter Smooth index scrollContainer)
    pure $ EventSource.Finalizer
      $ do
          unsubscribeSelectEventListener
          unsubscribeSnapEventListener
