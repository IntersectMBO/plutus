module Contract.Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Halogen (RefLabel)
import Marlowe.Execution (ExecutionState, NamedAction)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Semantics (Bound, ChoiceId, ChosenNum, Input, Slot, TransactionInput)
import Marlowe.Semantics as Semantic
import WalletData.Types (Nickname)

type State
  = { tab :: Tab
    , executionState :: ExecutionState
    , contractId :: Maybe String -- FIXME: what is a contract instance identified by
    , side :: Side
    , confirmation :: Maybe Input
    , step :: Int
    , metadata :: MetaData
    , participants :: Map Semantic.Party (Maybe Nickname)
    -- This field represents the logged-user party in the contract.
    -- If it's Nothing, then the logged-user is an observant of the contract. That could happen
    -- if the person who creates the contract does not put him/herself as a participant of the contract
    -- or if a Role participant sells the role token to another participant
    , mActiveUserParty :: Maybe Semantic.Party
    }

data Tab
  = Tasks
  | Balances

derive instance eqTab :: Eq Tab

data Side
  = Overview
  | Confirmation NamedAction

data Query a
  = ChangeSlot Slot a
  | ApplyTx TransactionInput a

data Action
  = ConfirmInput (Maybe Input)
  | ChangeChoice ChoiceId (Maybe ChosenNum)
  | ChooseInput (Maybe Input)
  | SelectTab Tab
  -- We have two levels of confirmation. The step confirmation is where we flip the
  -- contract card and show the selected action.
  | AskStepConfirmation NamedAction
  | CancelStepConfirmation
  -- The second confirmation shows wallet information as a new card on top of the
  -- contract card
  | AskWalletConfirmation NamedAction

instance actionIsEvent :: IsEvent Action where
  toEvent (ConfirmInput _) = Just $ defaultEvent "ConfirmInput"
  toEvent (ChangeChoice _ _) = Just $ defaultEvent "ChangeChoice"
  toEvent (ChooseInput _) = Just $ defaultEvent "ChooseInput"
  toEvent (SelectTab _) = Just $ defaultEvent "SelectTab"
  toEvent (AskStepConfirmation _) = Just $ defaultEvent "AskStepConfirmation"
  toEvent CancelStepConfirmation = Just $ defaultEvent "CancelStepConfirmation"
  toEvent (AskWalletConfirmation _) = Just $ defaultEvent "AskWalletConfirmation"
