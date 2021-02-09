module Contract.State where

import Prelude
import Contract.Types (Action(..), Query(..), Side(..), State, Tab(..), _confirmation, _executionState, _pk, _side, _step, _tab)
import Data.Lens (assign, modifying, use)
import Data.Maybe (Maybe(..))
import Data.Unfoldable as Unfoldable
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, raise)
import MainFrame.Types (ChildSlots, Msg(..))
import Marlowe.Execution (NamedAction(..), _namedActions, _state, initExecution, merge, mkTx, nextState)
import Marlowe.Semantics (ChoiceId(..), Contract, Input(..), Party(..), Slot, _minSlot)
import WebSocket (StreamToServer(..))

initialState :: String -> Slot -> Contract -> State
initialState pk slot contract =
  { tab: Tasks
  , executionState: initExecution slot contract
  , side: Overview
  , confirmation: Nothing
  , step: 0
  , pk
  }

handleQuery :: forall a m. Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ChangeSlot slot next) = do
  assign (_executionState <<< _state <<< _minSlot) slot
  pure $ Just next

handleQuery (ApplyTx tx next) = do
  modifying _executionState \currentExeState -> merge (nextState currentExeState tx) currentExeState
  pure $ Just next

getParty :: Input -> Maybe Party
getParty (IDeposit _ p _ _) = Just p

getParty (IChoice (ChoiceId _ p) _) = Just p

getParty _ = Nothing

handleAction :: forall m. MonadAff m => Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (ConfirmInput input) = do
  currentExeState <- use _executionState
  defaultParty <- use _pk
  let
    party = case input of
      (Just (IDeposit _ p _ _)) -> p
      (Just (IChoice (ChoiceId _ p) _)) -> p
      _ -> PK defaultParty

    txInput = mkTx currentExeState (Unfoldable.fromMaybe input)

    executionState = nextState currentExeState txInput
  assign _executionState executionState
  raise (SendWebSocketMessage (ServerMsg true)) -- FIXME: send txInput to the server to apply to the on-chain contract

handleAction (ChooseInput input) = assign _confirmation input

handleAction (ChangeChoice choiceId chosenNum) = modifying (_executionState <<< _namedActions) (map changeChoice)
  where
  changeChoice (MakeChoice choiceId' bounds _)
    | choiceId == choiceId' = MakeChoice choiceId bounds chosenNum

  changeChoice namedAction = namedAction

handleAction (SelectTab tab) = assign _tab tab

handleAction (FlipCard side) = assign _side side

-- Handled in MainFrame
handleAction ClosePanel = pure unit

handleAction (ChangeStep step) = assign _step step
