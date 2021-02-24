module Contract.State
  ( defaultState
  , mkInitialState
  , handleQuery
  , handleAction
  ) where

import Prelude
import Contract.Types (Action(..), Query(..), Side(..), State, Tab(..), _confirmation, _executionState, _side, _step, _tab)
import Data.Lens (assign, modifying, use)
import Data.Maybe (Maybe(..))
import Data.Unfoldable as Unfoldable
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Execution (NamedAction(..), _namedActions, _state, initExecution, merge, mkTx, nextState)
import Marlowe.Semantics (Contract(..), Slot, _minSlot)

defaultState :: State
defaultState = mkInitialState zero Close

mkInitialState :: Slot -> Contract -> State
mkInitialState slot contract =
  { tab: Tasks
  , executionState: initExecution slot contract
  , side: Overview
  , confirmation: Nothing
  , step: 0
  }

handleQuery :: forall a m. Query a -> HalogenM State Action ChildSlots Msg m (Maybe a)
handleQuery (ChangeSlot slot next) = do
  assign (_executionState <<< _state <<< _minSlot) slot
  pure $ Just next

handleQuery (ApplyTx tx next) = do
  modifying _executionState \currentExeState -> merge (nextState currentExeState tx) currentExeState
  pure $ Just next

handleAction :: forall m. MonadAff m => Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (ConfirmInput input) = do
  currentExeState <- use _executionState
  let
    txInput = mkTx currentExeState (Unfoldable.fromMaybe input)

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

handleAction (FlipCard side) = assign _side side

-- Handled in MainFrame
handleAction ClosePanel = pure unit

handleAction (ChangeStep step) = assign _step step
