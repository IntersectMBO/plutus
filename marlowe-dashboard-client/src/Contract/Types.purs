module Contract.Types
  ( State
  , PreviousStep
  , PreviousStepState(..)
  , Tab(..)
  , Input
  , Action(..)
  , scrollContainerRef
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Halogen (RefLabel(..))
import Marlowe.Execution.Types (NamedAction)
import Marlowe.Execution.Types (State) as Execution
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.PAB (PlutusAppId, MarloweParams)
import Marlowe.Semantics (ChoiceId, ChosenNum, Party, Slot, TransactionInput, Accounts)
import WalletData.Types (WalletDetails, WalletNickname)

-- The Contract.State wraps the Execution.State up with some additional information that is necessary
-- to render the execution state of the contract in the page. Some of this is derived data that could
-- be calculated on the fly, but is stored here for efficiency. The rest is data specific to the UX
-- (like which step card is currently centered, and which tabs are shown in which step cards).
type State
  = { followerAppId :: PlutusAppId
    , marloweParams :: MarloweParams
    , metadata :: MetaData
    , executionState :: Execution.State
    -- The following properties contain additional information on top of the Execution.State that is
    -- necessary to render the current state of the contract. Some of this information is just a function
    -- of the Execution.State, but is saved here for efficiency. (It needs to be recalculate when the
    -- Execution.State of the contract changes, but this way it doesn't need to be recalculated every time
    -- the user opens the card for this contract.
    ----------
    -- This is the tab of the current (latest) step card - previous step cards have their own tabs.
    , tab :: Tab
    -- These contain the data needed to render the previous step cards. This corresponds loosely to the
    -- array of PreviousTransactionSteps in the Execution.State, except that the shape and content of the
    -- data is slightly different, and we include timeout steps here in addition to transaction steps.
    , previousSteps :: Array PreviousStep
    -- Which step is selected. This index is 0 based and should be between [0, previousStepCards.length]
    -- (both sides inclusive). This is because the array represents the past steps and the Execution.State
    -- has the current state and visually we can select any one of them.
    , selectedStep :: Int
    , participants :: Map Party (Maybe WalletNickname)
    , userParties :: Set Party
    -- These are the possible actions a user can make in the current step. We store this mainly because
    -- extractNamedActions could potentially be unperformant to compute.
    , namedActions :: Array NamedAction
    }

type PreviousStep
  = { tab :: Tab
    , balances :: Accounts
    , state :: PreviousStepState
    }

data PreviousStepState
  = TransactionStep TransactionInput
  | TimeoutStep Slot

data Tab
  = Tasks
  | Balances

derive instance eqTab :: Eq Tab

-- The inputs provided to the Contract action handlers from the parent module (Play.State).
type Input
  = { currentSlot :: Slot
    , walletDetails :: WalletDetails
    }

data Action
  = ConfirmAction NamedAction
  | ChangeChoice ChoiceId (Maybe ChosenNum)
  | SelectTab Int Tab
  | AskConfirmation NamedAction
  | CancelConfirmation
  -- The SelectStep action is what changes the model and causes the card to seem bigger.
  | SelectStep Int
  -- The MoveToStep action scrolls the step carousel so that the indicated step is at the center (without changing the model).
  | MoveToStep Int
  | CarouselOpened
  | CarouselClosed

instance actionIsEvent :: IsEvent Action where
  toEvent (ConfirmAction _) = Just $ defaultEvent "ConfirmAction"
  toEvent (ChangeChoice _ _) = Just $ defaultEvent "ChangeChoice"
  toEvent (SelectTab _ _) = Just $ defaultEvent "SelectTab"
  toEvent (AskConfirmation _) = Just $ defaultEvent "AskConfirmation"
  toEvent CancelConfirmation = Just $ defaultEvent "CancelConfirmation"
  toEvent (SelectStep _) = Just $ defaultEvent "SelectStep"
  toEvent (MoveToStep _) = Nothing
  toEvent CarouselOpened = Just $ defaultEvent "CarouselOpened"
  toEvent CarouselClosed = Just $ defaultEvent "CarouselClosed"

scrollContainerRef :: RefLabel
scrollContainerRef = RefLabel "scroll-container"
