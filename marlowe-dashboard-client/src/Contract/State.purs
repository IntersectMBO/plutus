module Contract.State
  ( handleQuery
  , handleAction
  , mkInitialState
  , defaultState
  , currentStep
  ) where

import Prelude
import Contract.Lenses (_confirmation, _contractId, _executionState, _tab)
import Contract.Types (Action(..), Query(..), State, Tab(..))
import Control.Monad.Except (runExceptT)
import Control.Monad.Maybe.Trans (runMaybeT)
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.Reader.Extra (mapEnvReaderT)
import Data.Array (length)
import Data.Foldable (for_)
import Data.Lens (assign, modifying, to, use, view)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.RawJson (RawJson(..))
import Data.Unfoldable as Unfoldable
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Foreign.Generic (encode)
import Foreign.JSON (unsafeStringify)
import Halogen (HalogenM)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Execution (NamedAction(..), ExecutionStep, _namedActions, _state, _steps, initExecution, merge, mkTx, nextState)
import Marlowe.Extended (ContractType(..))
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Semantics (Contract(..), Slot, _minSlot)
import Marlowe.Semantics as Semantic
import Plutus.PAB.Webserver (postApiContractByContractinstanceidEndpointByEndpointname)
import WalletData.Types (Nickname)

-- I don't like having to provide emptyMetadata and default state
-- for this component, but it is needed by the mapMaybeSubmodule in
-- PlayState.
emptyMetadata :: MetaData
emptyMetadata =
  { contractType: Escrow
  , contractName: mempty
  , contractDescription: mempty
  , roleDescriptions: mempty
  , slotParameterDescriptions: mempty
  , valueParameterDescriptions: mempty
  , choiceDescriptions: mempty
  }

defaultState :: State
defaultState = mkInitialState zero Close emptyMetadata mempty Nothing

-- As programmers we use 0-indexed arrays and steps, but we number steps
-- starting from 1
currentStep :: State -> Int
currentStep = add 1 <<< length <<< view (_executionState <<< _steps)

mkInitialState ::
  Slot ->
  Contract ->
  MetaData ->
  Map Semantic.Party (Maybe Nickname) ->
  Maybe Semantic.Party ->
  State
mkInitialState slot contract metadata participants mActiveUserParty =
  { tab: Tasks
  , executionState: initExecution slot contract
  , confirmation: Nothing
  , contractId: Nothing
  , selectedStep: 0
  , metadata
  , participants
  , mActiveUserParty
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
handleAction (ConfirmInput input) = do
  currentExeState <- use _executionState
  mContractId <- use _contractId
  for_ mContractId \contractId -> do
    let
      txInput = mkTx currentExeState (Unfoldable.fromMaybe input)

      json = RawJson <<< unsafeStringify <<< encode $ input
    -- TODO: currently we just ignore errors but we probably want to do something better in the future
    runMaybeT do
      void $ mapEnvReaderT _.ajaxSettings $ runExceptT $ postApiContractByContractinstanceidEndpointByEndpointname json contractId "apply-inputs"
      let
        executionState = nextState currentExeState txInput
      assign _executionState executionState

-- raise (SendWebSocketMessage (ServerMsg true)) -- FIXME: send txInput to the server to apply to the on-chain contract
handleAction (ChooseInput input) = assign _confirmation input

handleAction (ChangeChoice choiceId chosenNum) = modifying (_executionState <<< _namedActions) (map changeChoice)
  where
  changeChoice (MakeChoice choiceId' bounds _)
    | choiceId == choiceId' = MakeChoice choiceId bounds chosenNum

  changeChoice namedAction = namedAction

handleAction (SelectTab tab) = assign _tab tab

handleAction (AskConfirmation action) = pure unit -- Managed by Play.State

handleAction CancelConfirmation = pure unit -- Managed by Play.State
