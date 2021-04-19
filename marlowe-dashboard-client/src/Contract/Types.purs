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
  , scrollContainerRef
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Halogen (RefLabel(..))
import Marlowe.Execution (ExecutionState, NamedAction)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Semantics (ChoiceId, ChosenNum, Contract, Party, Slot, TransactionInput, Accounts)
import Marlowe.Semantics (State) as Semantic
import Plutus.V1.Ledger.Value (CurrencySymbol)
import Types (ContractInstanceId)
import WalletData.Types (WalletNickname)

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

-- MarloweParams are used to identify a Marlowe contract in the PAB, and the wallet
-- companion contract state is a Map MarloweParams MarloweData. We are not currently
-- generating PureScript types to match the Haskell MarloweParams and MarloweData
-- types (side note: perhaps we should be). We have a CurrencySymbol type in
-- Marlowe.Semantics, but it is just an alias for String. We could use that here for
-- the `rolesCurrency` value, and convert using its Bridge instance when sharing data
-- with the PAB. However, we currently don't need to do anything with MarloweParams on
-- the frontend except save them and send them back to the PAB (to join a contract that
-- is already running), so it is simpler just to use the generated type in this case.
type MarloweParams
  = { rolePayoutValidatorHash :: ValidatorHash
    , rolesCurrency :: CurrencySymbol
    }

type ValidatorHash
  = String

type MarloweData
  = { marloweContract :: Contract
    , marloweState :: Semantic.State
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
  | SelectStep Int
  | MoveToStep Int
  | CarouselOpened
  | CarouselClosed

instance actionIsEvent :: IsEvent Action where
  toEvent (ConfirmAction _) = Just $ defaultEvent "ConfirmAction"
  toEvent (ChangeChoice _ _) = Just $ defaultEvent "ChangeChoice"
  toEvent (SelectTab _) = Just $ defaultEvent "SelectTab"
  toEvent (AskConfirmation _) = Just $ defaultEvent "AskConfirmation"
  toEvent CancelConfirmation = Just $ defaultEvent "CancelConfirmation"
  toEvent (SelectStep _) = Just $ defaultEvent "SelectStep"
  toEvent (MoveToStep _) = Just $ defaultEvent "MoveToStep"
  toEvent CarouselOpened = Just $ defaultEvent "CarouselOpened"
  toEvent CarouselClosed = Just $ defaultEvent "CarouselClosed"

scrollContainerRef :: RefLabel
scrollContainerRef = RefLabel "scroll-container"
