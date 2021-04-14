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
import Contract.Lenses (_contractId, _executionState, _namedActions, _previousSteps, _selectedStep, _tab)
import Contract.Types (Action(..), PreviousStep, PreviousStepState(..), Query(..), State, Tab(..))
import Control.Monad.Reader (class MonadAsk)
import Data.Array (length)
import Data.Lens (assign, modifying, over, to, toArrayOf, traversed, use, view, (^.))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.RawJson (RawJson(..))
import Data.Set as Set
import Data.Unfoldable as Unfoldable
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Effect.Exception.Unsafe (unsafeThrow)
import Env (Env)
import Foreign.Generic (encode)
import Foreign.JSON (unsafeStringify)
import Halogen (HalogenM, liftEffect, modify_)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Execution (NamedAction(..), PreviousState, _currentContract, _currentState, _pendingTimeouts, _previousState, expandBalances, extractNamedActions, initExecution, isClosed, mkTx, nextState, timeoutState)
import Marlowe.Extended (TemplateContent, fillTemplate, resolveRelativeTimes, toCore)
import Marlowe.Extended as Extended
import Marlowe.Extended.Metadata (MetaData, emptyContractMetadata)
import Marlowe.Semantics (Contract(..), Input(..), Slot, SlotInterval(..), Token(..), TransactionInput(..))
import Marlowe.Semantics as Semantic
import Marlowe.Slot (currentSlot)
import WalletData.Types (WalletNickname)

-- see note [dummyState]
dummyState :: State
dummyState = mkInitialState "" zero emptyContractMetadata mempty Nothing Close

currentStep :: State -> Int
currentStep = length <<< view _previousSteps

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
  String ->
  Slot ->
  Extended.Contract ->
  TemplateContent ->
  MetaData ->
  Map Semantic.Party (Maybe WalletNickname) ->
  Maybe Semantic.Party ->
  Maybe State
instantiateExtendedContract contractId currentSlot extendedContract templateContent metadata participants mActiveUserParty =
  let
    relativeContract = resolveRelativeTimes currentSlot extendedContract

    mContract = toCore $ fillTemplate templateContent relativeContract
  in
    mContract
      <#> mkInitialState contractId currentSlot metadata participants mActiveUserParty

mkInitialState ::
  String ->
  Slot ->
  MetaData ->
  Map Semantic.Party (Maybe WalletNickname) ->
  Maybe Semantic.Party ->
  Contract ->
  State
mkInitialState contractId slot metadata participants mActiveUserParty contract =
  let
    executionState = initExecution slot contract
  in
    { tab: Tasks
    , executionState
    , previousSteps: mempty
    , contractId
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
selectLastStep state@{ previousSteps } = state { selectedStep = length previousSteps }

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
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (ConfirmAction namedAction) = do
  currentExeState <- use _executionState
  contractId <- use _contractId
  slot <- liftEffect currentSlot
  let
    input = toInput namedAction

    txInput = mkTx slot (currentExeState ^. _currentContract) (Unfoldable.fromMaybe input)

    json = RawJson <<< unsafeStringify <<< encode $ input
  -- TODO: currently we just ignore errors but we probably want to do something better in the future
  -- FIXME: send data to BE
  -- void $ mapEnvReaderT _.ajaxSettings $ runExceptT $ postApiContractByContractinstanceidEndpointByEndpointname json contractId "apply-inputs"
  modify_ $ applyTx slot txInput

-- raise (SendWebSocketMessage (ServerMsg true)) -- FIXME: send txInput to the server to apply to the on-chain contract
handleAction (ChangeChoice choiceId chosenNum) = modifying _namedActions (map changeChoice)
  where
  changeChoice (MakeChoice choiceId' bounds _)
    | choiceId == choiceId' = MakeChoice choiceId bounds chosenNum

  changeChoice namedAction = namedAction

handleAction (SelectTab tab) = assign _tab tab

handleAction (AskConfirmation action) = pure unit -- Managed by Play.State

handleAction CancelConfirmation = pure unit -- Managed by Play.State

handleAction (GoToStep stepNumber) = assign _selectedStep stepNumber
