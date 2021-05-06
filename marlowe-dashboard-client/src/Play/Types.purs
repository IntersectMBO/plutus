module Play.Types
  ( State
  , Screen(..)
  , Card(..)
  , Inputs
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Contract.Types (Action) as Contract
import ContractHome.Types (Action, State) as ContractHome
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Minutes)
import Marlowe.Execution (NamedAction)
import Marlowe.Semantics (Slot, TokenName)
import Template.Types (Action, State) as Template
import Types (WebData)
import WalletData.Types (WalletDetails, WalletInfo, WalletLibrary, WalletNickname)

type State
  = { walletLibrary :: WalletLibrary
    , walletDetails :: WalletDetails
    , menuOpen :: Boolean
    , screen :: Screen
    , cards :: Array Card
    , newWalletNickname :: WalletNickname
    , newWalletCompanionAppIdString :: String
    , newWalletInfo :: WebData WalletInfo
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

type Inputs
  = { currentSlot :: Slot
    }

data Action
  = PutdownWallet
  | SetNewWalletNickname WalletNickname
  | SetNewWalletCompanionAppIdString String
  | SaveNewWallet (Maybe TokenName)
  | ToggleMenu
  | SetScreen Screen
  | OpenCard Card
  | CloseCard
  | AdvanceTimedoutSteps
  | TemplateAction Template.Action
  | ContractHomeAction ContractHome.Action
  | ContractAction Contract.Action

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent PutdownWallet = Just $ defaultEvent "PutdownWallet"
  toEvent (SetNewWalletNickname _) = Just $ defaultEvent "SetNewWalletNickname"
  toEvent (SetNewWalletCompanionAppIdString _) = Just $ defaultEvent "SetNewWalletCompanionAppId"
  toEvent (SaveNewWallet _) = Just $ defaultEvent "SaveNewWallet"
  toEvent ToggleMenu = Just $ defaultEvent "ToggleMenu"
  toEvent (SetScreen _) = Just $ defaultEvent "SetScreen"
  toEvent (OpenCard _) = Nothing
  toEvent CloseCard = Nothing
  toEvent AdvanceTimedoutSteps = Nothing
  toEvent (TemplateAction templateAction) = toEvent templateAction
  toEvent (ContractHomeAction contractAction) = toEvent contractAction
  toEvent (ContractAction contractAction) = toEvent contractAction
