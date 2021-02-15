module MainFrame.Types
  ( State
  , OutsideCard(..)
  , InsideState
  , Screen(..)
  , Card(..)
  , ContractStatus(..)
  , ContractTemplate
  , ContractInstance
  , ChildSlots
  , Query(..)
  , Msg(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Contract.Types as Contract
import Data.Maybe (Maybe(..))
import Marlowe.Semantics (Contract)
import Wallet.Types (PubKeyHash, WalletDetails, WalletLibrary, WalletNicknameKey)
import WebSocket (StreamToClient, StreamToServer)
import WebSocket.Support as WS

type State
  = { wallets :: WalletLibrary
    , newWalletNicknameKey :: WalletNicknameKey
    , outsideCard :: Maybe OutsideCard
    , insideState :: Maybe InsideState
    -- TODO: (work out how to) move contract state into inside state
    -- (the puzzle is how to handle contract actions in the mainframe if the
    -- submodule state is behind a `Maybe`... :thinking_face:)
    , contractState :: Contract.State
    }

data OutsideCard
  = PickupNewWalletCard
  | PickupWalletCard WalletNicknameKey

type InsideState
  = { wallet :: PubKeyHash
    , menuOpen :: Boolean
    , screen :: Screen
    , card :: Maybe Card
    , on :: Boolean
    }

data Screen
  = ContractsScreen ContractStatus
  | WalletLibraryScreen

derive instance eqFrame :: Eq Screen

data Card
  = CreateWalletCard
  | ViewWalletCard WalletNicknameKey WalletDetails
  | PutdownWalletCard
  | TemplateLibraryCard
  | ContractTemplateCard ContractTemplate
  | ContractInstanceCard ContractInstance

derive instance eqCard :: Eq Card

data ContractStatus
  = Running
  | Completed

derive instance eqContractStatus :: Eq ContractStatus

-- contract templage type TBD
type ContractTemplate
  = Int

-- contract instance type TBD
type ContractInstance
  = Int

------------------------------------------------------------
type ChildSlots
  = (
    )

------------------------------------------------------------
data Query a
  = ReceiveWebSocketMessage (WS.FromSocket StreamToClient) a

data Msg
  = SendWebSocketMessage StreamToServer

------------------------------------------------------------
data Action
  = Init
  -- outside actions
  | SetOutsideCard (Maybe OutsideCard)
  | GenerateNewWallet
  | PickupNewWallet
  | LookupWallet String
  | PickupWallet PubKeyHash
  -- inside actions
  | PutdownWallet
  | ToggleMenu
  | SetScreen Screen
  | SetCard (Maybe Card)
  | ToggleCard Card
  | SetNewWalletNickname String
  | SetNewWalletKey PubKeyHash
  | AddNewWallet
  | ClickedButton
  -- contract actions
  | ContractAction Contract.Action
  | StartContract Contract

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  -- outside actions
  toEvent (SetOutsideCard _) = Just $ defaultEvent "SetOutsideCard"
  toEvent GenerateNewWallet = Just $ defaultEvent "GenerateNewWallet"
  toEvent PickupNewWallet = Just $ defaultEvent "PickupNewWallet"
  toEvent (LookupWallet _) = Nothing
  toEvent (PickupWallet _) = Just $ defaultEvent "PickupWallet"
  -- inside actions
  toEvent PutdownWallet = Just $ defaultEvent "PutdownWallet"
  toEvent ToggleMenu = Just $ defaultEvent "ToggleMenu"
  toEvent (SetScreen _) = Just $ defaultEvent "SetScreen"
  toEvent (SetCard _) = Just $ defaultEvent "SetCard"
  toEvent (ToggleCard _) = Just $ defaultEvent "ToggleCard"
  toEvent (SetNewWalletNickname _) = Nothing
  toEvent (SetNewWalletKey _) = Nothing
  toEvent AddNewWallet = Just $ defaultEvent "AddNewWallet"
  toEvent ClickedButton = Just $ defaultEvent "ClickedButton"
  -- contract actions
  toEvent (ContractAction contractAction) = toEvent contractAction
  toEvent (StartContract _) = Just $ defaultEvent "StartContract"
