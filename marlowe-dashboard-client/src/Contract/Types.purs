module Contract.Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Maybe (Maybe(..))
import Marlowe.Execution (ExecutionState)
import Marlowe.Extended (MetaData)
import Marlowe.Semantics (ChoiceId, ChosenNum, Input, Slot, TransactionInput)

type State
  = { tab :: Tab
    , executionState :: ExecutionState
    , contractId :: Maybe String -- FIXME: what is a contract instance identified by
    , side :: Side
    , confirmation :: Maybe Input
    , step :: Int
    , metadata :: MetaData
    }

data Tab
  = Tasks
  | Balances

derive instance eqTab :: Eq Tab

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
