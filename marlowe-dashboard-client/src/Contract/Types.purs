module Contract.Types
  ( State
  , PreviousStep
  , PreviousStepState(..)
  , MarloweParams(..)
  , ValidatorHash
  , MarloweData(..)
  , Tab(..)
  , Query(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Execution (ExecutionState, NamedAction)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Semantics (ChoiceId, ChosenNum, Contract, CurrencySymbol, Party, Slot, TransactionInput, Accounts)
import Marlowe.Semantics (State) as Semantic
import WalletData.Types (WalletNickname)
import Types (ContractInstanceId)

type State
  = { tab :: Tab
    , executionState :: ExecutionState
    , previousSteps :: Array PreviousStep
    , contractInstanceId :: ContractInstanceId
    -- Which step is selected. This index is 0 based and should be between [0, previousSteps.length]
    -- (both sides inclusive). This is because the array represent the past steps and the
    -- executionState has the current state and visually we can select any one of them.
    , selectedStep :: Int
    , metadata :: MetaData
    , participants :: Map Party (Maybe WalletNickname)
    -- This field represents the logged-user party in the contract.
    -- If it's Nothing, then the logged-user is an observant of the contract. That could happen
    -- if the person who creates the contract does not put him/herself as a participant of the contract
    -- or if a Role participant sells the role token to another participant
    -- FIXME: The active party can use multiple roles, change this to (Array Party)
    , mActiveUserParty :: Maybe Party
    -- These are the possible actions a user can make in the current step. We store this mainly because
    -- extractNamedActions could potentially be unperformant to compute.
    , namedActions :: Array NamedAction
    }

-- Represents a historical step in a contract's life.
type PreviousStep
  = { balances :: Accounts
    , state :: PreviousStepState
    }

data PreviousStepState
  = TransactionStep TransactionInput
  | TimeoutStep Slot

-- FIXME: check serialization of this type works with the backend
newtype MarloweParams
  = MarloweParams
  { rolePayoutValidatorHash :: ValidatorHash
  , rolesCurrency :: CurrencySymbol
  }

derive instance newtypeMarloweParams :: Newtype MarloweParams _

derive instance eqMarloweParams :: Eq MarloweParams

derive instance genericMarloweParams :: Generic MarloweParams _

instance encodeMarloweParams :: Encode MarloweParams where
  encode value = genericEncode defaultOptions value

instance decodeMarloweParams :: Decode MarloweParams where
  decode value = genericDecode defaultOptions value

-- FIXME: check serialization of this type works with the backend
type ValidatorHash
  = String

-- note: the wallet companion contract state has type `Map MarloweParams MarloweData`
newtype MarloweData
  = MarloweData
  { marloweContract :: Contract
  , marloweState :: Semantic.State
  }

derive instance newtypeMarloweData :: Newtype MarloweData _

derive instance eqMarloweData :: Eq MarloweData

derive instance genericMarloweData :: Generic MarloweData _

instance encodeMarloweData :: Encode MarloweData where
  encode value = genericEncode defaultOptions value

instance decodeMarloweData :: Decode MarloweData where
  decode value = genericDecode defaultOptions value

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
