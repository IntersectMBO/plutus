module Dashboard.Types
  ( State
  , Screen(..)
  , Card(..)
  , ContractStatus(..)
  , PartitionedContracts
  , Input
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Contract.Types (Action, State) as Contract
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Minutes)
import InputField.Types (Action, State) as InputField
import Marlowe.Execution.Types (NamedAction)
import Marlowe.PAB (ContractHistory, MarloweData, MarloweParams, PlutusAppId)
import Marlowe.Semantics (Slot, TokenName)
import Template.Types (Action, State) as Template
import Types (WebData)
import WalletData.Types (WalletDetails, WalletInfo, WalletLibrary)
import WalletData.Validation (WalletIdError, WalletNicknameError)

type State
  = { walletLibrary :: WalletLibrary
    , walletDetails :: WalletDetails
    , menuOpen :: Boolean
    , screen :: Screen
    , cards :: Array Card
    , status :: ContractStatus
    , contracts :: Map PlutusAppId Contract.State
    , selectedContractIndex :: Maybe PlutusAppId
    , walletNicknameInput :: InputField.State WalletNicknameError
    , walletIdInput :: InputField.State WalletIdError
    , remoteWalletInfo :: WebData WalletInfo
    , timezoneOffset :: Minutes
    , templateState :: Template.State
    }

data Screen
  = ContractsScreen
  | WalletLibraryScreen
  | TemplateScreen

derive instance eqScreen :: Eq Screen

data Card
  = SaveWalletCard (Maybe String)
  | ViewWalletCard WalletDetails
  | PutdownWalletCard
  | TemplateLibraryCard
  | ContractSetupConfirmationCard
  | ContractCard
  | ContractActionConfirmationCard NamedAction

derive instance eqCard :: Eq Card

data ContractStatus
  = Running
  | Completed

derive instance eqContractStatus :: Eq ContractStatus

type PartitionedContracts
  = { completed :: Array Contract.State, running :: Array Contract.State }

type Input
  = { currentSlot :: Slot
    }

data Action
  = PutdownWallet
  | WalletNicknameInputAction (InputField.Action WalletNicknameError)
  | WalletIdInputAction (InputField.Action WalletIdError)
  | SetRemoteWalletInfo (WebData WalletInfo)
  | SaveNewWallet (Maybe TokenName)
  | ToggleMenu
  | SetScreen Screen
  | OpenCard Card
  | CloseCard Card
  | SelectView ContractStatus
  | OpenContract PlutusAppId
  | UpdateFromStorage
  | UpdateFollowerApps (Map MarloweParams MarloweData)
  | UpdateContract PlutusAppId ContractHistory
  | AdvanceTimedoutSteps
  | TemplateAction Template.Action
  | ContractAction Contract.Action

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent PutdownWallet = Just $ defaultEvent "PutdownWallet"
  toEvent (WalletNicknameInputAction inputAction) = toEvent inputAction
  toEvent (WalletIdInputAction inputAction) = toEvent inputAction
  toEvent (SetRemoteWalletInfo _) = Nothing
  toEvent (SaveNewWallet _) = Just $ defaultEvent "SaveNewWallet"
  toEvent ToggleMenu = Just $ defaultEvent "ToggleMenu"
  toEvent (SetScreen _) = Just $ defaultEvent "SetScreen"
  toEvent (OpenCard _) = Nothing
  toEvent (CloseCard _) = Nothing
  toEvent (SelectView _) = Just $ defaultEvent "SelectView"
  toEvent (OpenContract _) = Just $ defaultEvent "OpenContract"
  toEvent UpdateFromStorage = Nothing
  toEvent (UpdateFollowerApps _) = Nothing
  toEvent (UpdateContract _ _) = Nothing
  toEvent AdvanceTimedoutSteps = Nothing
  toEvent (TemplateAction templateAction) = toEvent templateAction
  toEvent (ContractAction contractAction) = toEvent contractAction
