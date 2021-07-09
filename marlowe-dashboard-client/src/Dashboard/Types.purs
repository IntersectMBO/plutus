module Dashboard.Types
  ( State
  , Card(..)
  , ContractFilter(..)
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
    , card :: Maybe Card
    , cardOpen :: Boolean -- see note [CardOpen] in Welcome.State (the same applies here)
    , contracts :: Map PlutusAppId Contract.State
    , contractFilter :: ContractFilter
    , selectedContractIndex :: Maybe PlutusAppId
    , walletNicknameInput :: InputField.State WalletNicknameError
    , walletIdInput :: InputField.State WalletIdError
    , remoteWalletInfo :: WebData WalletInfo
    , timezoneOffset :: Minutes
    , templateState :: Template.State
    }

data Card
  = TutorialsCard
  | CurrentWalletCard
  | WalletLibraryCard
  | SaveWalletCard (Maybe String)
  | ViewWalletCard WalletDetails
  | TemplateLibraryCard
  | ContractSetupCard
  | ContractSetupConfirmationCard
  | ContractActionConfirmationCard NamedAction

derive instance eqCard :: Eq Card

data ContractFilter
  = Running
  | Completed

derive instance eqContractFilter :: Eq ContractFilter

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
  | OpenCard Card
  | CloseCard
  | SetContractFilter ContractFilter
  | SelectContract (Maybe PlutusAppId)
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
  toEvent (OpenCard _) = Nothing
  toEvent CloseCard = Nothing
  toEvent (SetContractFilter _) = Just $ defaultEvent "FilterContracts"
  toEvent (SelectContract _) = Just $ defaultEvent "OpenContract"
  toEvent UpdateFromStorage = Nothing
  toEvent (UpdateFollowerApps _) = Nothing
  toEvent (UpdateContract _ _) = Nothing
  toEvent AdvanceTimedoutSteps = Nothing
  toEvent (TemplateAction templateAction) = toEvent templateAction
  toEvent (ContractAction contractAction) = toEvent contractAction
