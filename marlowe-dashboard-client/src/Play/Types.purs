module Play.Types
  ( State
  , Screen(..)
  , Card(..)
  , Input
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Contract.Types (Action) as Contract
import ContractHome.Types (Action, State) as ContractHome
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Minutes)
import InputField.Types (Action, State) as InputField
import Marlowe.Execution.Types (NamedAction)
import Marlowe.PAB (MarloweData, MarloweParams)
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
    , walletNicknameInput :: InputField.State WalletNicknameError
    , walletIdInput :: InputField.State WalletIdError
    , remoteWalletInfo :: WebData WalletInfo
    , timezoneOffset :: Minutes
    , templateState :: Template.State
    , contractsState :: ContractHome.State
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
  | UpdateFromStorage
  | UpdateRunningContracts (Map MarloweParams MarloweData)
  | AdvanceTimedoutSteps
  | TemplateAction Template.Action
  | ContractHomeAction ContractHome.Action
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
  toEvent UpdateFromStorage = Nothing
  toEvent (UpdateRunningContracts _) = Nothing
  toEvent AdvanceTimedoutSteps = Nothing
  toEvent (TemplateAction templateAction) = toEvent templateAction
  toEvent (ContractHomeAction contractAction) = toEvent contractAction
  toEvent (ContractAction contractAction) = toEvent contractAction
