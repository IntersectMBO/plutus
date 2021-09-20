module Simulator.Types where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Foreign.Generic (class Decode, class Encode, genericDecode, genericEncode)
import Marlowe.Template (TemplateContent)
import Marlowe.Holes (Holes, Term)
import Marlowe.Holes as T
import Marlowe.Semantics (AccountId, Assets, Bound, ChoiceId, ChosenNum, Input, Party(..), Payment, Slot, SlotInterval, Token, TransactionError, TransactionInput, TransactionWarning, aesonCompatibleOptions)
import Marlowe.Semantics as S
import Monaco (IMarker)

data ActionInputId
  = DepositInputId AccountId Party Token BigInteger
  | ChoiceInputId ChoiceId
  | NotifyInputId
  | MoveToSlotId

derive instance eqActionInputId :: Eq ActionInputId

derive instance ordActionInputId :: Ord ActionInputId

derive instance genericActionInputId :: Generic ActionInputId _

instance encodeActionInputId :: Encode ActionInputId where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeActionInputId :: Decode ActionInputId where
  decode = genericDecode aesonCompatibleOptions

-- | On the front end we need Actions however we also need to keep track of the current
-- | choice that has been set for Choices
data ActionInput
  = DepositInput AccountId Party Token BigInteger
  | ChoiceInput ChoiceId (Array Bound) ChosenNum
  | NotifyInput
  | MoveToSlot Slot

derive instance eqActionInput :: Eq ActionInput

derive instance ordActionInput :: Ord ActionInput

derive instance genericActionInput :: Generic ActionInput _

instance encodeActionInput :: Encode ActionInput where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeActionInput :: Decode ActionInput where
  decode = genericDecode aesonCompatibleOptions

-- TODO: Probably rename to PartiesActions or similar
newtype Parties
  = Parties (Map Party (Map ActionInputId ActionInput))

derive instance newtypeParties :: Newtype Parties _

derive newtype instance semigroupParties :: Semigroup Parties

derive newtype instance monoidParties :: Monoid Parties

derive newtype instance encodeParties :: Encode Parties

derive newtype instance decodeParties :: Decode Parties

-- We have a special person for notifications
otherActionsParty :: Party
otherActionsParty = Role "marlowe_other_actions"

data LogEntry
  = StartEvent Slot
  | InputEvent TransactionInput
  | OutputEvent SlotInterval Payment
  | CloseEvent SlotInterval

derive instance genericLogEntry :: Generic LogEntry _

instance encodeLogEntry :: Encode LogEntry where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeLogEntry :: Decode LogEntry where
  decode = genericDecode aesonCompatibleOptions

type ExecutionStateRecord
  = { possibleActions :: Parties
    , pendingInputs :: Array Input
    , transactionError :: Maybe TransactionError
    , transactionWarnings :: Array TransactionWarning
    , log :: Array LogEntry
    , state :: S.State
    , slot :: Slot
    , moneyInContract :: Assets
    -- This is the remaining of the contract to be executed
    , contract :: Term T.Contract
    }

type InitialConditionsRecord
  = { initialSlot :: Slot
    -- TODO: Should we remove the Maybe and just not set InitialConditionsRecord if we cannot
    --       parse the contract?
    , termContract :: Maybe (Term T.Contract)
    , templateContent :: TemplateContent
    }

data ExecutionState
  = SimulationRunning ExecutionStateRecord
  | SimulationNotStarted InitialConditionsRecord

type MarloweState
  = { executionState :: ExecutionState
    , holes :: Holes
    -- NOTE: as part of the marlowe editor and simulator split this part of the
    --       state wont be used, but it is left as it is because it may make sense
    --       to use it as part of task SCP-1642
    , editorErrors :: Array IMarker
    , editorWarnings :: Array IMarker
    }
