module Play.Types
  ( State
  , Screen(..)
  , Card(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Contract.Types (Action) as Contract
import ContractHome.Types (Action, State) as ContractHome
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Minutes)
import Marlowe.Execution (NamedAction)
import Marlowe.Semantics (Slot)
import Template.Types (Action, State) as Template
import WalletData.Types (WalletDetails, WalletNickname)

type State
  = { walletDetails :: WalletDetails
    , menuOpen :: Boolean
    , screen :: Screen
    , cards :: Array Card
    , currentSlot :: Slot
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
  = CreateWalletCard (Maybe String)
  | ViewWalletCard WalletDetails
  | PutdownWalletCard
  | TemplateLibraryCard
  | ContractSetupConfirmationCard
  | ContractCard
  | ContractActionConfirmationCard NamedAction

derive instance eqCard :: Eq Card

data Action
  = PutdownWallet
  | SetNewWalletNickname WalletNickname
  | SetNewWalletContractId String
  | AddNewWallet (Maybe String)
  | ToggleMenu
  | SetScreen Screen
  | OpenCard Card
  | CloseCard
  | TemplateAction Template.Action
  | ContractAction Contract.Action
  | ContractHomeAction ContractHome.Action
  | SetCurrentSlot Slot

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent PutdownWallet = Just $ defaultEvent "PutdownWallet"
  toEvent (SetNewWalletNickname _) = Just $ defaultEvent "SetNewWalletNickname"
  toEvent (SetNewWalletContractId _) = Just $ defaultEvent "SetNewWalletContractId"
  toEvent (AddNewWallet _) = Just $ defaultEvent "AddNewWallet"
  toEvent ToggleMenu = Just $ defaultEvent "ToggleMenu"
  toEvent (SetScreen _) = Just $ defaultEvent "SetScreen"
  toEvent (OpenCard _) = Nothing
  toEvent CloseCard = Nothing
  toEvent (TemplateAction templateAction) = toEvent templateAction
  toEvent (ContractAction contractAction) = toEvent contractAction
  toEvent (ContractHomeAction contractAction) = toEvent contractAction
  toEvent (SetCurrentSlot _) = Nothing
