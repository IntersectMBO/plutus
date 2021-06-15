module Contract.State
  ( dummyState
  , mkInitialState
  , updateState
  , handleAction
  , currentStep
  , isContractClosed
  , applyTx
  , applyTimeout
  ) where

import Prelude
import Capability.Marlowe (class ManageMarlowe, applyTransactionInput)
import Capability.Toast (class Toast, addToast)
import Contract.Lenses (_executionState, _marloweParams, _namedActions, _previousSteps, _selectedStep, _tab)
import Contract.Types (Action(..), Input, PreviousStep, PreviousStepState(..), State, Tab(..), scrollContainerRef)
import Control.Monad.Reader (class MonadAsk, asks)
import Data.Array (difference, filter, foldl, index, length, mapMaybe, modifyAt)
import Data.Either (Either(..))
import Data.Foldable (foldMap, for_)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Lens (assign, modifying, over, to, toArrayOf, traversed, use, view, (^.))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Ord (abs)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple.Nested ((/\))
import Data.UUID as UUID
import Data.Unfoldable as Unfoldable
import Effect (Effect)
import Effect.Aff.AVar as AVar
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Exception.Unsafe (unsafeThrow)
import Env (Env)
import Halogen (HalogenM, getHTMLElementRef, gets, liftEffect, subscribe, unsubscribe)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Deinstantiate (findTemplate)
import Marlowe.Execution.Lenses (_currentContract, _currentState, _pendingTimeouts, _previousState, _previousTransactions)
import Marlowe.Execution.State (expandBalances, extractNamedActions, initExecution, isClosed, mkTx, nextState, timeoutState)
import Marlowe.Execution.Types (ExecutionState, NamedAction(..), PreviousState)
import Marlowe.Extended.Metadata (emptyContractMetadata)
import Marlowe.HasParties (getParties)
import Marlowe.PAB (ContractHistory, PlutusAppId(..), MarloweParams)
import Marlowe.Semantics (Contract(..), Party(..), Slot, SlotInterval(..), TransactionInput(..), _minSlot)
import Marlowe.Semantics (Input(..), State(..)) as Semantic
import Plutus.V1.Ledger.Value (CurrencySymbol(..))
import Toast.Types (ajaxErrorToast, successToast)
import WalletData.Lenses (_assets, _pubKeyHash, _walletInfo)
import WalletData.State (adaToken)
import WalletData.Types (WalletDetails)
import Web.DOM.Element (getElementsByClassName)
import Web.DOM.HTMLCollection as HTMLCollection
import Web.Dom.ElementExtra (Alignment(..), ScrollBehavior(..), debouncedOnScroll, scrollIntoView, throttledOnScroll)
import Web.HTML (HTMLElement)
import Web.HTML.HTMLElement (getBoundingClientRect, offsetLeft)
import Web.HTML.HTMLElement as HTMLElement

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState =
  { tab: Tasks
  , executionState: initExecution zero contract
  , previousSteps: mempty
  , marloweParams: emptyMarloweParams
  , followerAppId: emptyPlutusAppId
  , selectedStep: 0
  , metadata: emptyContractMetadata
  , participants: mempty
  , userParties: mempty
  , namedActions: mempty
  }
  where
  contract = Close

  emptyPlutusAppId = PlutusAppId UUID.emptyUUID

  emptyMarloweParams = { rolePayoutValidatorHash: mempty, rolesCurrency: CurrencySymbol { unCurrencySymbol: "" } }

  emptyMarloweData = { marloweContract: contract, marloweState: emptyMarloweState }

  emptyMarloweState = Semantic.State { accounts: mempty, choices: mempty, boundValues: mempty, minSlot: zero }

mkInitialState :: WalletDetails -> Slot -> PlutusAppId -> ContractHistory -> Maybe State
mkInitialState walletDetails currentSlot followerAppId { chParams, chHistory } =
  bind chParams \(marloweParams /\ marloweData) ->
    let
      contract = marloweData.marloweContract

      mTemplate = findTemplate contract

      minSlot = view _minSlot marloweData.marloweState

      initialExecutionState = initExecution minSlot contract
    in
      flip map mTemplate \template ->
        let
          isRoleParty party = case party of
            Role _ -> true
            _ -> false

          -- Note we filter out PK parties here. This is because we don't have a design for displaying
          -- them anywhere, and because we are currently only using one in a special case (in the Escrow
          -- with Collateral contract), where it doesn't make much sense to show it to the user anyway.
          -- If we ever want to use PK parties for other purposes, we will need to rethink this.
          roleParties :: Array Party
          roleParties = filter isRoleParty $ Set.toUnfoldable $ getParties contract

          initialState =
            { tab: Tasks
            , executionState: initialExecutionState
            , previousSteps: mempty
            , marloweParams
            , followerAppId
            , selectedStep: 0
            , metadata: template.metaData
            , participants: Map.fromFoldable $ map (\x -> x /\ Nothing) roleParties
            , userParties: getUserParties walletDetails marloweParams
            , namedActions: mempty
            }

          updateExecutionState = over _executionState (applyTransactionInputs chHistory)
        in
          initialState
            # updateExecutionState
            # regenerateStepCards currentSlot
            # selectLastStep

updateState :: Slot -> Array TransactionInput -> State -> State
updateState currentSlot transactionInputs state =
  let
    previousTransactionInputs = toArrayOf (_executionState <<< _previousTransactions) state

    newTransactionInputs = difference transactionInputs previousTransactionInputs

    updateExecutionState = over _executionState (applyTransactionInputs newTransactionInputs)
  in
    state
      # updateExecutionState
      # regenerateStepCards currentSlot
      # selectLastStep

getUserParties :: WalletDetails -> MarloweParams -> Set Party
getUserParties walletDetails marloweParams =
  let
    pubKeyHash = view (_walletInfo <<< _pubKeyHash) walletDetails

    assets = view _assets walletDetails

    currencySymbolString = (unwrap marloweParams.rolesCurrency).unCurrencySymbol

    mCurrencyTokens = Map.lookup currencySymbolString (unwrap assets)

    roleTokens = foldMap (Set.map Role <<< Map.keys <<< Map.filter ((/=) zero)) mCurrencyTokens
  in
    Set.insert (PK $ unwrap pubKeyHash) roleTokens

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  ManageMarlowe m =>
  Toast m =>
  Input -> Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction input@{ currentSlot, walletDetails } (ConfirmAction namedAction) = do
  currentExeState <- use _executionState
  marloweParams <- use _marloweParams
  let
    contractInput = toInput namedAction

    txInput = mkTx currentSlot (currentExeState ^. _currentContract) (Unfoldable.fromMaybe contractInput)
  ajaxApplyInputs <- applyTransactionInput walletDetails marloweParams txInput
  case ajaxApplyInputs of
    Left ajaxError -> addToast $ ajaxErrorToast "Failed to submit transaction." ajaxError
    Right _ -> do
      stepNumber <- gets currentStep
      handleAction input (MoveToStep stepNumber)
      addToast $ successToast "Payment received, step completed."

handleAction _ (ChangeChoice choiceId chosenNum) = modifying _namedActions (map changeChoice)
  where
  changeChoice (MakeChoice choiceId' bounds _)
    | choiceId == choiceId' = MakeChoice choiceId bounds chosenNum

  changeChoice namedAction = namedAction

handleAction _ (SelectTab stepNumber tab) = do
  previousSteps <- use _previousSteps
  case modifyAt stepNumber (\previousStep -> previousStep { tab = tab }) previousSteps of
    -- if the stepNumber is in the range of the previousSteps, we update that step
    Just modifiedPreviousSteps -> assign _previousSteps modifiedPreviousSteps
    -- otherwise we update the tab of the current step
    Nothing -> assign _tab tab

handleAction _ (AskConfirmation action) = pure unit -- Managed by Play.State

handleAction _ CancelConfirmation = pure unit -- Managed by Play.State

handleAction _ (SelectStep stepNumber) = assign _selectedStep stepNumber

handleAction _ (MoveToStep stepNumber) = do
  -- The MoveToStep action is called when a new step is added (either via an apply transaction or
  -- a timeout). We unsubscribe and resubscribe to update the tracked elements.
  unsubscribeFromSelectCenteredStep
  subscribeToSelectCenteredStep
  mElement <- getHTMLElementRef scrollContainerRef
  for_ mElement $ liftEffect <<< scrollStepToCenter Smooth stepNumber

handleAction _ CarouselOpened = do
  selectedStep <- use _selectedStep
  mElement <- getHTMLElementRef scrollContainerRef
  for_ mElement \elm -> do
    -- When the carousel is opened we want to assure that the selected step is
    -- in the center without any animation
    liftEffect $ scrollStepToCenter Auto selectedStep elm
    subscribeToSelectCenteredStep

handleAction _ CarouselClosed = unsubscribeFromSelectCenteredStep

applyTransactionInputs :: Array TransactionInput -> ExecutionState -> ExecutionState
applyTransactionInputs transactionInputs state = foldl nextState state transactionInputs

currentStep :: State -> Int
currentStep = length <<< view _previousSteps

isContractClosed :: State -> Boolean
isContractClosed state = isClosed $ state ^. _executionState

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

toInput :: NamedAction -> Maybe Semantic.Input
toInput (MakeDeposit accountId party token value) = Just $ Semantic.IDeposit accountId party token value

toInput (MakeChoice choiceId _ (Just chosenNum)) = Just $ Semantic.IChoice choiceId chosenNum

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

toInput (MakeNotify _) = Just $ Semantic.INotify

toInput _ = Nothing

transactionsToStep :: State -> PreviousState -> PreviousStep
transactionsToStep { participants } { txInput, state } =
  let
    TransactionInput { interval: SlotInterval minSlot maxSlot, inputs } = txInput

    -- TODO: When we add support for multiple tokens we should extract the possible tokens from the
    --       contract, store it in ContractState and pass them here.
    balances = expandBalances (Set.toUnfoldable $ Map.keys participants) [ adaToken ] state

    stepState =
      -- For the moment the only way to get an empty transaction is if there was a timeout,
      -- but later on there could be other reasons to move a contract forward, and we should
      -- compare with the contract to see the reason.
      if inputs == mempty then
        TimeoutStep minSlot
      else
        TransactionStep txInput
  in
    { tab: Tasks
    , balances
    , state: stepState
    }

timeoutToStep :: State -> Slot -> PreviousStep
timeoutToStep { participants, executionState } slot =
  let
    currentContractState = executionState ^. _currentState

    balances = expandBalances (Set.toUnfoldable $ Map.keys participants) [ adaToken ] currentContractState
  in
    { tab: Tasks
    , balances
    , state: TimeoutStep slot
    }

regenerateStepCards :: Slot -> State -> State
regenerateStepCards currentSlot state =
  -- TODO: This regenerates all the previous step cards, resetting them to their default state (showing
  -- the Tasks tab). If any of them are showing the Balances tab, it would be nice to keep them that way.
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
selectLastStep state@{ previousSteps } = state { selectedStep = length previousSteps }

------------------------------------------------------------------
-- NOTE: In the first version of the selectCenteredStep feature the subscriptionId was stored in the
--       Contract.State as a Maybe SubscriptionId. But when calling subscribe/unsubscribe multiple
--       times in a small period of time there was a concurrency issue and multiple subscriptions
--       were active at the same time, which caused scroll issues. We use an AVar to control the
--       concurrency and assure that only one subscription is active at a time.
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
  mStepElement <- flip index stepNumber <$> getStepElemets
  for_ mStepElement $ scrollIntoView { block: Center, inline: Center, behavior }

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
    stepLeftOffsets <- traverse offsetLeft $ mapMaybe HTMLElement.fromElement stepElements
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
    -- https://bugs.chromium.org/p/chromium/issues/detail?id=1195682
    unsubscribeSnapEventListener <-
      debouncedOnScroll
        150.0
        (HTMLElement.toElement scrollContainer)
        $ \scrollPos -> do
            let
              index = calculateClosestStep scrollPos
            scrollStepToCenter Smooth index scrollContainer
            EventSource.emit emitter $ SelectStep index
    pure $ EventSource.Finalizer
      $ do
          unsubscribeSelectEventListener
          unsubscribeSnapEventListener
