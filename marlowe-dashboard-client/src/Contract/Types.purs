module Contract.Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Marlowe.Execution (ExecutionState, NamedAction)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Semantics (ChoiceId, ChosenNum, Slot, TransactionInput, Accounts)
import Marlowe.Semantics as Semantic
import WalletData.Types (Nickname)

-- Represents a historical step in a contract's life.
type PreviousStep
  = { balances :: Accounts
    , state :: PreviousStepState
    }

data PreviousStepState
  = TransactionStep TransactionInput
  | TimeoutStep Slot

type State
  = { tab :: Tab
    , executionState :: ExecutionState
    , previousSteps :: Array PreviousStep
    , contractId :: String -- FIXME: what is a contract instance identified by
    -- Which step is selected. This index is 0 based and should be between [0, previousSteps.length]
    -- (both sides inclusive). This is because the array represent the past steps and the
    -- executionState has the current state and visually we can select any one of them.
    , selectedStep :: Int
    , metadata :: MetaData
    , participants :: Map Semantic.Party (Maybe Nickname)
    -- This field represents the logged-user party in the contract.
    -- If it's Nothing, then the logged-user is an observant of the contract. That could happen
    -- if the person who creates the contract does not put him/herself as a participant of the contract
    -- or if a Role participant sells the role token to another participant
    -- FIXME: The active party can use multiple roles, change this to (Array Party)
    , mActiveUserParty :: Maybe Semantic.Party
    -- These are the possible actions a user can make in the current step. We store this mainly because
    -- extractNamedActions could potentially be unperformant to compute.
    , namedActions :: Array NamedAction
    }

data Tab
  = Tasks
  | Balances

derive instance eqTab :: Eq Tab

data Query a
  = ApplyTx TransactionInput a

data Action
  = ConfirmAction NamedAction
  | ChangeChoice ChoiceId (Maybe ChosenNum)
  | SelectTab Tab
  | AskConfirmation NamedAction
  | CancelConfirmation
  | GoToStep Int

instance actionIsEvent :: IsEvent Action where
  toEvent (ConfirmAction _) = Just $ defaultEvent "ConfirmAction"
  toEvent (ChangeChoice _ _) = Just $ defaultEvent "ChangeChoice"
  toEvent (SelectTab _) = Just $ defaultEvent "SelectTab"
  toEvent (AskConfirmation _) = Just $ defaultEvent "AskConfirmation"
  toEvent CancelConfirmation = Just $ defaultEvent "CancelConfirmation"
  toEvent (GoToStep _) = Just $ defaultEvent "GoToStep"
