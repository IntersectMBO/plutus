module Play.Types
  ( State
  , Screen(..)
  , ContractStatus(..)
  , Card(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Contract.Types (Action, State) as Contract
import Data.Maybe (Maybe(..))
import Marlowe.Semantics (PubKey)
import Template.Types (Action, Screen, State) as Template
import WalletData.Types (WalletDetails, WalletNicknameKey)

type State
  = { wallet :: PubKey
    , menuOpen :: Boolean
    , screen :: Screen
    , card :: Maybe Card
    , templateState :: Template.State
    , contractState :: Contract.State
    }

data Screen
  = ContractsScreen ContractStatus
  | WalletLibraryScreen
  | TemplateScreen Template.Screen

derive instance eqScreen :: Eq Screen

data Card
  = CreateWalletCard
  | ViewWalletCard WalletNicknameKey WalletDetails
  | PutdownWalletCard
  | TemplateLibraryCard
  | NewContractForRoleCard
  | ContractSetupConfirmationCard
  | ContractCard

derive instance eqCard :: Eq Card

data ContractStatus
  = Running
  | Completed

derive instance eqContractStatus :: Eq ContractStatus

data Action
  = PutdownWallet
  | SetNewWalletNickname String
  | SetNewWalletKey PubKey
  | AddNewWallet
  | ToggleMenu
  | SetScreen Screen
  | SetCard (Maybe Card)
  | ToggleCard Card
  | TemplateAction Template.Action
  | ContractAction Contract.Action

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent PutdownWallet = Just $ defaultEvent "PutdownWallet"
  toEvent (SetNewWalletNickname _) = Just $ defaultEvent "SetNewWalletNickname"
  toEvent (SetNewWalletKey _) = Just $ defaultEvent "SetNewWalletKey"
  toEvent AddNewWallet = Just $ defaultEvent "AddNewWallet"
  toEvent ToggleMenu = Just $ defaultEvent "ToggleMenu"
  toEvent (SetScreen _) = Just $ defaultEvent "SetScreen"
  toEvent (SetCard _) = Just $ defaultEvent "SetCard"
  toEvent (ToggleCard _) = Just $ defaultEvent "ToggleCard"
  toEvent (TemplateAction templateAction) = toEvent templateAction
  toEvent (ContractAction contractAction) = toEvent contractAction
