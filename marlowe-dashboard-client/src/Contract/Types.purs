module Contract.Types
  ( State
  , PreviousStep
  , PreviousStepState(..)
  , Tab(..)
  , Inputs
  , Action(..)
  , scrollContainerRef
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Halogen (RefLabel(..))
import Marlowe.Execution (ExecutionState, NamedAction)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.PAB (PlutusAppId, MarloweParams)
import Marlowe.Semantics (ChoiceId, ChosenNum, Party, Slot, TransactionInput, Accounts)
import WalletData.Types (WalletDetails, WalletNickname)

type State
  = { tab :: Tab
    , executionState :: ExecutionState
    , previousSteps :: Array PreviousStep
    , followerAppId :: PlutusAppId
    , marloweParams :: MarloweParams
    -- Which step is selected. This index is 0 based and should be between [0, previousSteps.length]
    -- (both sides inclusive). This is because the array represent the past steps and the
    -- executionState has the current state and visually we can select any one of them.
    , selectedStep :: Int
    , metadata :: MetaData
    , participants :: Map Party (Maybe WalletNickname)
    , userParties :: Set Party
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

data Tab
  = Tasks
  | Balances

derive instance eqTab :: Eq Tab

type Inputs
  = { currentSlot :: Slot
    , walletDetails :: WalletDetails
    }

data Action
  = ConfirmAction NamedAction
  | ChangeChoice ChoiceId (Maybe ChosenNum)
  | SelectTab Tab
  | AskConfirmation NamedAction
  | CancelConfirmation
  -- The SelectStep action is what changes the model and causes the card to seem bigger.
  | SelectStep Int
  -- The MoveToStep action scrolls the step carousel so that the indicated step is at the center
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
