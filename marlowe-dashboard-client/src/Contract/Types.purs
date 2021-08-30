module Contract.Types
  ( State
  , StepBalance
  , TimeoutInfo
  , PreviousStep
  , PreviousStepState(..)
  , Tab(..)
  , Input
  , Movement(..)
  , Action(..)
  , scrollContainerRef
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.BigInteger (BigInteger)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Time.Duration (Minutes)
import Data.Tuple (Tuple)
import Halogen (RefLabel(..))
import Marlowe.Execution.Types (NamedAction)
import Marlowe.Execution.Types (State) as Execution
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Client (MarloweAppEndpoint)
import Marlowe.PAB (PlutusAppId)
import Marlowe.Semantics (AccountId, Accounts, ChoiceId, ChosenNum, MarloweParams, Party, Payment, Slot, Token, TransactionInput)
import WalletData.Types (WalletDetails, WalletNickname)

type State
  = { nickname :: String
    , tab :: Tab -- this is the tab of the current (latest) step - previous steps have their own tabs
    , executionState :: Execution.State
    -- When the user submits a transaction, we save it here until we get confirmation from the PAB and
    -- can advance the contract. This enables us to show immediate feedback to the user while we wait.
    , pendingTransaction :: Maybe TransactionInput
    , previousSteps :: Array PreviousStep
    -- Every contract needs MarloweParams, but this is a Maybe because we want to create "placeholder"
    -- contracts when a user creates a contract, to show on the page until the blockchain settles and
    -- we get the MarloweParams back from the PAB (through the MarloweFollower app).
    , mMarloweParams :: Maybe MarloweParams
    -- Which step is selected. This index is 0 based and should be between [0, previousSteps.length]
    -- (both sides inclusive). This is because the array represent the past steps and the
    -- executionState has the current state and visually we can select any one of them.
    , selectedStep :: Int
    , metadata :: MetaData
    , participants :: Map Party (Maybe WalletNickname)
    -- Theser are the roles and PK's that the "logged-in" user has in this contract.
    , userParties :: Set Party
    -- These are the possible actions a user can make in the current step (grouped by part). We store this
    -- mainly because extractNamedActions and expandAndGroupByRole could potentially be unperformant to compute
    -- for every render.
    , namedActions :: Array (Tuple Party (Array NamedAction))
    }

type StepBalance
  = { atStart :: Accounts
    , atEnd :: Maybe Accounts
    }

-- Represents a historical step in a contract's life.
type PreviousStep
  = { tab :: Tab
    , expandPayments :: Boolean
    , resultingPayments :: Array Payment
    , balances :: StepBalance
    , state :: PreviousStepState
    }

type TimeoutInfo
  = { slot :: Slot
    , missedActions :: Array (Tuple Party (Array NamedAction))
    }

data PreviousStepState
  = TransactionStep TransactionInput
  | TimeoutStep TimeoutInfo

data Tab
  = Tasks
  | Balances

derive instance eqTab :: Eq Tab

type Input
  = { currentSlot :: Slot
    , tzOffset :: Minutes
    , walletDetails :: WalletDetails
    , followerAppId :: PlutusAppId
    , lastMarloweAppEndpointCall :: Maybe MarloweAppEndpoint
    }

data Movement
  = PayIn Party AccountId Token BigInteger -- a.k.a deposit
  | Transfer Party Party Token BigInteger
  | PayOut AccountId Party Token BigInteger

data Action
  = SelectSelf
  | SetNickname String
  | ConfirmAction NamedAction
  | ChangeChoice ChoiceId (Maybe ChosenNum)
  | SelectTab Int Tab
  | ToggleExpandPayment Int
  | AskConfirmation NamedAction
  | CancelConfirmation
  -- The SelectStep action is what changes the model and causes the card to seem bigger.
  | SelectStep Int
  -- The MoveToStep action scrolls the step carousel so that the indicated step is at the center (without changing the model).
  | MoveToStep Int
  | CarouselOpened
  | CarouselClosed

instance actionIsEvent :: IsEvent Action where
  toEvent SelectSelf = Nothing
  toEvent (ConfirmAction _) = Just $ defaultEvent "ConfirmAction"
  toEvent (SetNickname _) = Just $ defaultEvent "SetNickname"
  toEvent (ChangeChoice _ _) = Just $ defaultEvent "ChangeChoice"
  toEvent (SelectTab _ _) = Just $ defaultEvent "SelectTab"
  toEvent (ToggleExpandPayment _) = Just $ defaultEvent "ToggleExpandPayment"
  toEvent (AskConfirmation _) = Just $ defaultEvent "AskConfirmation"
  toEvent CancelConfirmation = Just $ defaultEvent "CancelConfirmation"
  toEvent (SelectStep _) = Just $ defaultEvent "SelectStep"
  toEvent (MoveToStep _) = Nothing
  toEvent CarouselOpened = Just $ defaultEvent "CarouselOpened"
  toEvent CarouselClosed = Just $ defaultEvent "CarouselClosed"

scrollContainerRef :: RefLabel
scrollContainerRef = RefLabel "scroll-container"
