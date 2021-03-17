module Contract.State
  ( handleQuery
  , handleAction
  , mkInitialState
  , defaultState
  ) where

import Prelude
import Contract.Lenses (_choiceValidStatus, _confirmation, _contractId, _executionState, _side, _step, _tab)
import Contract.Types (Action(..), Query(..), Side(..), State, Tab(..))
import Control.Monad.Except (runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader (class MonadAsk)
import Control.Monad.Reader.Extra (mapEnvReaderT)
import Data.BigInteger (BigInteger, fromString)
import Data.Foldable (for_)
import Data.Lens (assign, modifying, use)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.RawJson (RawJson(..))
import Data.Unfoldable as Unfoldable
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Foreign.Generic (encode)
import Foreign.JSON (unsafeStringify)
import Halogen (HalogenM, RefLabel(..), getHTMLElementRef, liftEffect)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Execution (NamedAction(..), _namedActions, _state, initExecution, merge, mkTx, nextState)
import Marlowe.Extended (ContractType(..))
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Semantics (Bound(..), ChoiceId(..), Contract(..), Slot, _minSlot, getEncompassBound)
import Marlowe.Semantics as Semantic
import Plutus.PAB.Webserver (postApiContractByContractinstanceidEndpointByEndpointname)
import WalletData.Types (Nickname)
import Web.HTML.HTMLInputElement as HTMLInputElement

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
  , side: Overview
  , confirmation: Nothing
  , contractId: Nothing
  , step: 0
  , metadata
  , participants
  , mActiveUserParty
  , choiceValidStatus: mempty
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

-- This action handler checks if an option is between bounds and updates a map that
-- controls the enabled/disabled property on the submit button.
handleAction (OnChoiceChange ref bounds) =
  void
    $ runMaybeT do
        element <- MaybeT $ getHTMLElementRef ref
        inputElement <- hoistMaybe $ HTMLInputElement.fromHTMLElement element
        stringValue <- MaybeT $ map pure $ liftEffect $ HTMLInputElement.value inputElement
        let
          Bound minBound maxBound = getEncompassBound bounds

          -- This maybe is outside the scope of the runMaybeT, because if we can't parse
          -- the stringValue as a BigInteger, the number is invalid and we want to store that
          -- in the map, and runMaybeT stops executing at the first Nothing.
          isValid = maybe false (between minBound maxBound) $ fromString stringValue
        modifying _choiceValidStatus $ Map.insert ref isValid

handleAction (AskStepConfirmation (MakeChoice c@(ChoiceId choiceId _) bounds _)) =
  let
    ref = RefLabel choiceId
  in
    void
      $ runMaybeT do
          element <- MaybeT $ getHTMLElementRef ref
          inputElement <- hoistMaybe $ HTMLInputElement.fromHTMLElement element
          bigIntegerValue <- MaybeT $ map fromString $ liftEffect $ HTMLInputElement.value inputElement
          -- NOTE: We omit the `between` validation step here as the button should not be clickable if the choice is
          --       invalid, and that is managed by `OnChoiceChange`
          assign _side $ Confirmation $ MakeChoice c bounds bigIntegerValue

handleAction (AskStepConfirmation action) = assign _side $ Confirmation action

handleAction CancelStepConfirmation = assign _side Overview

handleAction (AskWalletConfirmation _) = pure unit -- FIXME: we need to make cards a stack, and this handler should push a new validation card into it
