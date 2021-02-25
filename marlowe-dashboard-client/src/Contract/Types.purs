module Contract.Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Marlowe.Execution (ExecutionState)
import Marlowe.Semantics (ChoiceId, ChosenNum, Input, Slot, TransactionInput)

data Tab
  = Tasks
  | Balances

data Side
  = Overview
  | Confirmation

data Query a
  = ChangeSlot Slot a
  | ApplyTx TransactionInput a

data Action
  = ConfirmInput (Maybe Input)
  | ChangeChoice ChoiceId ChosenNum
  | ChooseInput (Maybe Input)
  | SelectTab Tab
  | FlipCard Side
  | ClosePanel
  | ChangeStep Int

instance actionIsEvent :: IsEvent Action where
  toEvent (ConfirmInput _) = Just $ defaultEvent "ConfirmInput"
  toEvent (ChangeChoice _ _) = Just $ defaultEvent "ChangeChoice"
  toEvent (ChooseInput _) = Just $ defaultEvent "ChooseInput"
  toEvent (SelectTab _) = Just $ defaultEvent "SelectTab"
  toEvent (FlipCard _) = Just $ defaultEvent "FlipCard"
  toEvent ClosePanel = Just $ defaultEvent "ClosePanel"
  toEvent (ChangeStep _) = Just $ defaultEvent "ChangeStep"

type State
  = { tab :: Tab
    , executionState :: ExecutionState
    , contractId :: Maybe String -- FIXME: what is a contract instance identified by
    , side :: Side
    , confirmation :: Maybe Input
    , step :: Int
    }

_tab :: Lens' State Tab
_tab = prop (SProxy :: SProxy "tab")

_executionState :: Lens' State ExecutionState
_executionState = prop (SProxy :: SProxy "executionState")

_side :: Lens' State Side
_side = prop (SProxy :: SProxy "side")

_confirmation :: Lens' State (Maybe Input)
_confirmation = prop (SProxy :: SProxy "confirmation")

_step :: Lens' State Int
_step = prop (SProxy :: SProxy "step")

_contractId :: Lens' State (Maybe String)
_contractId = prop (SProxy :: SProxy "contractId")
