module Contract.State
  ( dummyState
  , mkPlaceholderState
  , mkInitialState
  , updateState
  , handleAction
  , currentStep
  , isContractClosed
  , applyTx
  , applyTimeout
  ) where

import Prelude
import Capability.MainFrameLoop (class MainFrameLoop, callMainFrameAction)
import Capability.Marlowe (class ManageMarlowe, applyTransactionInput)
import Capability.MarloweStorage (class ManageMarloweStorage, insertIntoContractNicknames)
import Capability.Toast (class Toast, addToast)
import Contract.Lenses (_executionState, _mMarloweParams, _namedActions, _nickname, _participants, _pendingTransaction, _previousSteps, _selectedStep, _tab, _userParties)
import Contract.Types (Action(..), Input, PreviousStep, PreviousStepState(..), State, Tab(..), scrollContainerRef)
import Control.Monad.Reader (class MonadAsk, asks)
import Control.Monad.Reader.Class (ask)
import Dashboard.Types (Action(..)) as Dashboard
import Data.Array (difference, filter, foldl, index, length, mapMaybe, modifyAt)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (foldMap, for_)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Lens (assign, modifying, over, set, to, toArrayOf, traversed, use, view, (^.))
import Data.Lens.Lens.Tuple (_2)
import Data.List (toUnfoldable)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing)
import Data.Newtype (unwrap)
import Data.Ord (abs)
import Data.Set (Set)
import Data.Set as Set
import Data.Time.Duration (Milliseconds(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Data.Unfoldable as Unfoldable
import Effect (Effect)
import Effect.Aff.AVar as AVar
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Exception.Unsafe (unsafeThrow)
import Env (DataProvider(..), Env)
import Halogen (HalogenM, getHTMLElementRef, liftEffect, query, subscribe, tell, unsubscribe)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import LoadingSubmitButton.Types (Query(..), _submitButtonSlot)
import MainFrame.Types (Action(..)) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Deinstantiate (findTemplate)
import Marlowe.Execution.Lenses (_contract, _semanticState, _history, _pendingTimeouts, _previousTransactions)
import Marlowe.Execution.State (expandBalances, extractNamedActions, getActionParticipant, isClosed, mkTx, nextState, timeoutState)
import Marlowe.Execution.State (mkInitialState) as Execution
import Marlowe.Execution.Types (NamedAction(..), PastAction(..))
import Marlowe.Execution.Types (PastState, State, TimeoutInfo) as Execution
import Marlowe.Extended.Metadata (MetaData, emptyContractMetadata)
import Marlowe.HasParties (getParties)
import Marlowe.Client (ContractHistory, MarloweAppEndpoint(..), _chHistory, _chParams)
import Marlowe.Semantics (Contract(..), MarloweParams(..), Party(..), Slot, SlotInterval(..), TransactionInput(..), _accounts, _marloweContract, _marloweState, _minSlot, _rolesCurrency)
import Marlowe.Semantics (Input(..), State(..)) as Semantic
import Toast.Types (ajaxErrorToast, errorToast, successToast)
import WalletData.Lenses (_assets, _pubKeyHash, _walletInfo)
import WalletData.State (adaToken)
import WalletData.Types (WalletDetails, WalletNickname)
import Web.DOM.Element (getElementsByClassName)
import Web.DOM.HTMLCollection as HTMLCollection
import Web.Dom.ElementExtra (Alignment(..), ScrollBehavior(..), debouncedOnScroll, scrollIntoView, throttledOnScroll)
import Web.HTML (HTMLElement)
import Web.HTML.HTMLElement (getBoundingClientRect, offsetLeft)
import Web.HTML.HTMLElement as HTMLElement

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState =
  { nickname: mempty
  , tab: Tasks
  , executionState: Execution.mkInitialState zero contract
  , pendingTransaction: Nothing
  , previousSteps: mempty
  , mMarloweParams: Nothing
  , selectedStep: 0
  , metadata: emptyContractMetadata
  , participants: mempty
  , userParties: mempty
  , namedActions: mempty
  }
  where
  contract = Close

  emptyMarloweData = { marloweContract: contract, marloweState: emptyMarloweState }

  emptyMarloweState = Semantic.State { accounts: mempty, choices: mempty, boundValues: mempty, minSlot: zero }

-- this is for making a placeholder state for the user who created the contract, used for displaying
-- something before we get the MarloweParams back from the WalletCompanion app
mkPlaceholderState :: String -> MetaData -> Contract -> State
mkPlaceholderState nickname metaData contract =
  { nickname
  , tab: Tasks
  , executionState: Execution.mkInitialState zero contract
  , pendingTransaction: Nothing
  , previousSteps: mempty
  , mMarloweParams: Nothing
  , selectedStep: 0
  , metadata: metaData
  , participants: getParticipants contract
  , userParties: mempty
  , namedActions: mempty
  }

-- this is for making a fully fleshed out state from nothing, used when someone who didn't create the
-- contract is given a role in it, and gets the MarloweParams at the same time as they hear about
-- everything else
mkInitialState :: WalletDetails -> Slot -> String -> ContractHistory -> Maybe State
mkInitialState walletDetails currentSlot nickname contractHistory =
  let
    chParams = view _chParams contractHistory
  in
    bind chParams \(marloweParams /\ marloweData) ->
      let
        chHistory = view _chHistory contractHistory

        contract = view _marloweContract marloweData

        mTemplate = findTemplate contract

        minSlot = view (_marloweState <<< _minSlot) marloweData

        initialExecutionState = Execution.mkInitialState minSlot contract
      in
        flip map mTemplate \template ->
          let
            initialState =
              { nickname
              , tab: Tasks
              , executionState: initialExecutionState
              , pendingTransaction: Nothing
              , previousSteps: mempty
              , mMarloweParams: Just marloweParams
              , selectedStep: 0
              , metadata: template.metaData
              , participants: getParticipants contract
              , userParties: getUserParties walletDetails marloweParams
              , namedActions: mempty
              }

            updateExecutionState = over _executionState (applyTransactionInputs chHistory)
          in
            initialState
              # updateExecutionState
              # regenerateStepCards currentSlot
              # selectLastStep

-- Note 1: We filter out PK parties from the participants of the contract. This is because
-- we don't have a design for displaying them anywhere, and because we are currently only
-- using one in a special case (in the Escrow with Collateral contract), where it doesn't
-- make much sense to show it to the user anyway. If we ever want to use PK parties for
-- other purposes, we will need to rethink this.
-- Note 2: In general there is no way to map parties to wallet nicknames. It is possible
-- for the user who created the contract and distributed the role tokens, but this
-- information will be lost when the browser is closed. And other participants don't have
-- this information in the first place. Also, in the future it could be possible to give
-- role tokens to other wallets, and we wouldn't know about that either. Still, we're
-- keeping the `Maybe WalletNickname` in here for now, in case a way of making it generally
-- available (e.g. through the metadata server) ever becomes apparent.
getParticipants :: Contract -> Map Party (Maybe WalletNickname)
getParticipants contract = Map.fromFoldable $ map (\x -> x /\ Nothing) (getRoleParties contract)

getRoleParties :: Contract -> Array Party
getRoleParties contract = filter isRoleParty $ Set.toUnfoldable $ getParties contract
  where
  isRoleParty party = case party of
    Role _ -> true
    _ -> false

updateState :: WalletDetails -> MarloweParams -> Slot -> Array TransactionInput -> State -> State
updateState walletDetails marloweParams currentSlot transactionInputs state =
  let
    previousTransactionInputs = toArrayOf (_executionState <<< _previousTransactions) state

    newTransactionInputs = difference transactionInputs previousTransactionInputs

    -- If the `MarloweParams` are `Nothing`, that means this is the first update we've received for
    -- a placeholder contract, and we'll need to set the `MarloweParams` now and also work out the
    -- `userParties` (because these depend on the `MarloweParams`).
    mSetParamsAndParties =
      if isNothing $ state ^. _mMarloweParams then
        set _mMarloweParams (Just marloweParams)
          <<< set _userParties (getUserParties walletDetails marloweParams)
      else
        identity

    -- If there are new transaction inputs to apply, we need to clear the `pendingTransaction`. If
    -- we wanted to be really careful, we could check that the new transaction input matches the
    -- pending one, but I can't see how it wouldn't (and I don't think it matters anyway).
    mClearPendingTransaction =
      if newTransactionInputs /= mempty then
        set _pendingTransaction Nothing
      else
        identity

    updateExecutionState = over _executionState (applyTransactionInputs newTransactionInputs)
  in
    state
      # mSetParamsAndParties
      # mClearPendingTransaction
      # updateExecutionState
      # regenerateStepCards currentSlot
      # selectLastStep

getUserParties :: WalletDetails -> MarloweParams -> Set Party
getUserParties walletDetails marloweParams =
  let
    pubKeyHash = view (_walletInfo <<< _pubKeyHash) walletDetails

    assets = view _assets walletDetails

    rolesCurrency = view _rolesCurrency marloweParams

    mCurrencyTokens = Map.lookup rolesCurrency (unwrap assets)

    roleTokens = foldMap (Set.map Role <<< Map.keys <<< Map.filter ((/=) zero)) mCurrencyTokens
  in
    Set.insert (PK $ unwrap pubKeyHash) roleTokens

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  MainFrameLoop m =>
  ManageMarlowe m =>
  ManageMarloweStorage m =>
  Toast m =>
  Input -> Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction { followerAppId } SelectSelf = callMainFrameAction $ MainFrame.DashboardAction $ Dashboard.SelectContract $ Just followerAppId

handleAction { followerAppId } (SetNickname nickname) = do
  assign _nickname nickname
  insertIntoContractNicknames followerAppId nickname

handleAction input@{ currentSlot, walletDetails, lastMarloweAppEndpointCall } (ConfirmAction namedAction) = do
  case lastMarloweAppEndpointCall of
    Nothing -> do
      executionState <- use _executionState
      mMarloweParams <- use _mMarloweParams
      for_ mMarloweParams \marloweParams -> do
        let
          contractInput = toInput namedAction

          txInput = mkTx currentSlot (executionState ^. _contract) (Unfoldable.fromMaybe contractInput)
        callMainFrameAction $ MainFrame.DashboardAction $ Dashboard.SetLastMarloweAppEndpointCall $ Just ApplyInputs
        ajaxApplyInputs <- applyTransactionInput walletDetails marloweParams txInput
        case ajaxApplyInputs of
          Left ajaxError -> do
            void $ query _submitButtonSlot "action-confirm-button" $ tell $ SubmitResult (Milliseconds 600.0) (Left "Error")
            addToast $ ajaxErrorToast "Failed to submit transaction." ajaxError
          Right _ -> do
            assign _pendingTransaction $ Just txInput
            void $ query _submitButtonSlot "action-confirm-button" $ tell $ SubmitResult (Milliseconds 600.0) (Right "")
            addToast $ successToast "Transaction submitted, awating confirmation."
            { dataProvider } <- ask
            when (dataProvider == LocalStorage) (callMainFrameAction $ MainFrame.DashboardAction $ Dashboard.UpdateFromStorage)
    Just _ -> addToast $ errorToast "Application busy. Please try again in a moment." $ Just "We are still waiting to hear back from the previous action you submitted. Once you see a notification about that action, you can try to update this contract again."

handleAction _ (ChangeChoice choiceId chosenNum) = modifying (_namedActions <<< traversed <<< _2 <<< traversed) changeChoice
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

handleAction _ (ToggleExpandPayment stepNumber) = do
  previousSteps <- use _previousSteps
  case modifyAt stepNumber (\previousStep -> previousStep { expandPayments = not previousStep.expandPayments }) previousSteps of
    -- TODO: after expanding we should scroll the summary into view
    Just modifiedPreviousSteps -> assign _previousSteps modifiedPreviousSteps
    Nothing -> pure unit

handleAction _ (AskConfirmation action) = pure unit -- Managed by Dashboard.State

handleAction _ CancelConfirmation = pure unit -- Managed by Dashboard.State

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

applyTransactionInputs :: Array TransactionInput -> Execution.State -> Execution.State
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
      # set _pendingTransaction Nothing
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

transactionsToStep :: State -> Execution.PastState -> PreviousStep
transactionsToStep state { balancesAtStart, balancesAtEnd, txInput, resultingPayments, action } =
  let
    TransactionInput { interval: SlotInterval minSlot maxSlot, inputs } = txInput

    participants = state ^. _participants

    -- TODO: When we add support for multiple tokens we should extract the possible tokens from the
    --       contract, store it in ContractState and pass them here.
    expandedBalancesAtStart = expandBalances (Set.toUnfoldable $ Map.keys participants) [ adaToken ] balancesAtStart

    expandedBalancesAtEnd = expandBalances (Set.toUnfoldable $ Map.keys participants) [ adaToken ] balancesAtEnd

    stepState = case action of
      TimeoutAction act ->
        let
          userParties = state ^. _userParties

          missedActions =
            expandAndGroupByRole
              userParties
              (Map.keys participants)
              act.missedActions
        in
          TimeoutStep { slot: act.slot, missedActions }
      InputAction -> TransactionStep txInput
  in
    { tab: Tasks
    , expandPayments: false
    , resultingPayments: toUnfoldable resultingPayments
    , balances:
        { atStart:
            expandedBalancesAtStart
        , atEnd: Just expandedBalancesAtEnd
        }
    , state: stepState
    }

timeoutToStep :: State -> Execution.TimeoutInfo -> PreviousStep
timeoutToStep state { slot, missedActions } =
  let
    balances = state ^. (_executionState <<< _semanticState <<< _accounts)

    userParties = state ^. _userParties

    participants = state ^. _participants

    expandedBalances = expandBalances (Set.toUnfoldable $ Map.keys participants) [ adaToken ] balances
  in
    { tab: Tasks
    , expandPayments: false
    -- FIXME: Revisit how should we treat payments from timeout steps, for now they are not displayed
    , resultingPayments: []
    , balances:
        { atStart: expandedBalances
        , atEnd: Nothing
        }
    , state:
        TimeoutStep
          { slot
          , missedActions:
              expandAndGroupByRole
                userParties
                (Map.keys participants)
                missedActions
          }
    }

regenerateStepCards :: Slot -> State -> State
regenerateStepCards currentSlot state =
  -- TODO: This regenerates all the previous step cards, resetting them to their default state (showing
  -- the Tasks tab). If any of them are showing the Balances tab, it would be nice to keep them that way.
  -- TODO: Performance optimization
  --  This function is being called for all cotracts whenever any contract change. We should be able to call it
  --  only for the changed contract. Moreover, we regenerate previous steps for the selected contract card and the
  --  summary cards in the dashboard, but only the selected contract cares about the previous steps, the dashboard
  --  only needs the current step and the step number.
  let
    confirmedSteps :: Array PreviousStep
    confirmedSteps = toArrayOf (_executionState <<< _history <<< traversed <<< to (transactionsToStep state)) state

    pendingTimeoutSteps :: Array PreviousStep
    pendingTimeoutSteps = toArrayOf (_executionState <<< _pendingTimeouts <<< traversed <<< to (timeoutToStep state)) state

    previousSteps = confirmedSteps <> pendingTimeoutSteps

    executionState = state ^. _executionState

    userParties = state ^. _userParties

    participants = state ^. _participants

    namedActions =
      expandAndGroupByRole
        userParties
        (Map.keys participants)
        (extractNamedActions currentSlot executionState)
  in
    state { previousSteps = previousSteps, namedActions = namedActions }

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

  isUserParty party = Set.member party userParties

  currentPartiesFirst (Tuple party1 _) (Tuple party2 _)
    | isUserParty party1 == isUserParty party2 = compare party1 party2
    | otherwise = if isUserParty party1 then LT else GT

  sameParty a b = fst a == fst b

  extractGroupedParty :: NonEmptyArray (Tuple Party NamedAction) -> Tuple Party (Array NamedAction)
  extractGroupedParty group = case NonEmptyArray.unzip group of
    tokens /\ actions' -> NonEmptyArray.head tokens /\ NonEmptyArray.toArray actions'

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
