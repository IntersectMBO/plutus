module Dashboard.Types
  ( State
  , Card(..)
  , ContractFilter(..)
  , Input
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Contract.Types (Action, State) as Contract
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Minutes)
import Marlowe.Execution.Types (NamedAction)
import Marlowe.PAB (ContractHistory, MarloweData, MarloweParams, PlutusAppId)
import Marlowe.Semantics (Slot)
import Template.Types (Action, State) as Template
import WalletData.Types (Action, State) as WalletData
import WalletData.Types (WalletDetails, WalletNickname)

type State
  = { walletDataState :: WalletData.State
    , walletDetails :: WalletDetails
    , menuOpen :: Boolean
    , card :: Maybe Card
    , cardOpen :: Boolean -- see note [CardOpen] in Welcome.State (the same applies here)
    , contracts :: Map PlutusAppId Contract.State
    , contractFilter :: ContractFilter
    , selectedContractFollowerAppId :: Maybe PlutusAppId
    , timezoneOffset :: Minutes
    , templateState :: Template.State
    }

data Card
  = TutorialsCard
  | CurrentWalletCard
  | WalletDataCard
  | ContractTemplateCard
  | ContractActionConfirmationCard PlutusAppId NamedAction

derive instance eqCard :: Eq Card

data ContractFilter
  = Running
  | Completed

derive instance eqContractFilter :: Eq ContractFilter

type Input
  = { currentSlot :: Slot
    }

data Action
  = PutdownWallet
  | WalletDataAction WalletData.Action
  | ToggleMenu
  | OpenCard Card
  | CloseCard
  | SetContractFilter ContractFilter
  | SelectContract (Maybe PlutusAppId)
  | UpdateFromStorage
  | UpdateFollowerApps (Map MarloweParams MarloweData)
  | UpdateContract PlutusAppId ContractHistory
  | RedeemPayments PlutusAppId
  | AdvanceTimedoutSteps
  | TemplateAction Template.Action
  | ContractAction PlutusAppId Contract.Action
  | SetContactForRole String WalletNickname

-- | Here we decide which top-level queries to track as GA events, and how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent PutdownWallet = Just $ defaultEvent "PutdownWallet"
  toEvent (WalletDataAction walletDataAction) = toEvent walletDataAction
  toEvent ToggleMenu = Just $ defaultEvent "ToggleMenu"
  toEvent (OpenCard _) = Nothing
  toEvent CloseCard = Nothing
  toEvent (SetContractFilter _) = Just $ defaultEvent "FilterContracts"
  toEvent (SelectContract _) = Just $ defaultEvent "OpenContract"
  toEvent UpdateFromStorage = Nothing
  toEvent (UpdateFollowerApps _) = Nothing
  toEvent (UpdateContract _ _) = Nothing
  toEvent (RedeemPayments _) = Nothing
  toEvent AdvanceTimedoutSteps = Nothing
  toEvent (TemplateAction templateAction) = toEvent templateAction
  toEvent (ContractAction _ contractAction) = toEvent contractAction
  toEvent (SetContactForRole _ _) = Nothing
