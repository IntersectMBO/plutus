module Contract.State
  ( handleQuery
  , handleAction
  , mkInitialState
  , instantiateExtendedContract
  , defaultState
  , currentStep
  , isContractClosed
  ) where

import Prelude
import Contract.Lenses (_contractId, _executionState, _mNextTimeout, _selectedStep, _tab)
import Contract.Types (Action(..), Query(..), State, Tab(..))
import Control.Monad.Maybe.Trans (runMaybeT)
import Control.Monad.Reader (class MonadAsk)
import Data.Array (length)
import Data.Lens (assign, modifying, set, use, view, (^.))
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.RawJson (RawJson(..))
import Data.Unfoldable as Unfoldable
import Effect.Aff.Class (class MonadAff)
import Effect.Exception.Unsafe (unsafeThrow)
import Env (Env)
import Foreign.Generic (encode)
import Foreign.JSON (unsafeStringify)
import Halogen (HalogenM, modify_)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Execution (NamedAction(..), _contract, _namedActions, _state, _steps, initExecution, merge, mkTx, nextState)
import Marlowe.Extended (TemplateContent, fillTemplate, resolveRelativeTimes, toCore)
import Marlowe.Extended as Extended
import Marlowe.Extended.Metadata (MetaData, emptyContractMetadata)
import Marlowe.Semantics (Contract(..), Input(..), Slot, Timeouts(..), _minSlot, timeouts)
import Marlowe.Semantics as Semantic
import WalletData.Types (Nickname)

-- I don't like having to provide a default state for this component, but it is needed by the
-- mapMaybeSubmodule in PlayState.
defaultState :: State
defaultState = mkInitialState "" zero emptyContractMetadata mempty Nothing Close

currentStep :: State -> Int
currentStep = length <<< view (_executionState <<< _steps)

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
isContractClosed state = state ^. (_executionState <<< _contract) == Close

instantiateExtendedContract ::
  String ->
  Slot ->
  Extended.Contract ->
  TemplateContent ->
  MetaData ->
  Map Semantic.Party (Maybe Nickname) ->
  Maybe Semantic.Party ->
  Maybe State
instantiateExtendedContract contractId currentSlot extendedContract templateContent metadata participants mActiveUserParty =
  let
    relativeContract = resolveRelativeTimes currentSlot extendedContract

    mContract = toCore $ fillTemplate templateContent relativeContract
  in
    mContract
      <#> mkInitialState contractId currentSlot metadata participants mActiveUserParty

nextTimeout :: Contract -> Maybe Slot
nextTimeout = timeouts >>> \(Timeouts { minTime }) -> minTime

mkInitialState ::
  String ->
  Slot ->
  MetaData ->
  Map Semantic.Party (Maybe Nickname) ->
  Maybe Semantic.Party ->
  Contract ->
  State
mkInitialState contractId slot metadata participants mActiveUserParty contract =
  { tab: Tasks
  , executionState: initExecution slot contract
  , contractId
  , selectedStep: 0
  , metadata
  , participants
  , mActiveUserParty
  , mNextTimeout: nextTimeout contract
  }

handleQuery :: forall a m. Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ChangeSlot slot next) = do
  assign (_executionState <<< _state <<< _minSlot) slot
  pure $ Just next

handleQuery (ApplyTx tx next) = do
  modifying _executionState \currentExeState -> merge (nextState currentExeState tx) currentExeState
  pure $ Just next

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (ConfirmAction action) = do
  currentExeState <- use _executionState
  contractId <- use _contractId
  let
    input = toInput action

    txInput = mkTx currentExeState (Unfoldable.fromMaybe input)

    json = RawJson <<< unsafeStringify <<< encode $ input
  -- TODO: currently we just ignore errors but we probably want to do something better in the future
  void
    $ runMaybeT do
        -- FIXME: send data to BE
        -- void $ mapEnvReaderT _.ajaxSettings $ runExceptT $ postApiContractByContractinstanceidEndpointByEndpointname json contractId "apply-inputs"
        let
          executionState = nextState currentExeState txInput

          mNextTimeout = nextTimeout (executionState ^. _contract)
        modify_
          ( set _executionState executionState
              <<< set _selectedStep (length executionState.steps)
              <<< set _mNextTimeout mNextTimeout
          )

-- raise (SendWebSocketMessage (ServerMsg true)) -- FIXME: send txInput to the server to apply to the on-chain contract
handleAction (ChangeChoice choiceId chosenNum) = modifying (_executionState <<< _namedActions) (map changeChoice)
  where
  changeChoice (MakeChoice choiceId' bounds _)
    | choiceId == choiceId' = MakeChoice choiceId bounds chosenNum

  changeChoice namedAction = namedAction

handleAction (SelectTab tab) = assign _tab tab

handleAction (AskConfirmation action) = pure unit -- Managed by Play.State

handleAction CancelConfirmation = pure unit -- Managed by Play.State

handleAction (GoToStep stepNumber) = assign _selectedStep stepNumber
