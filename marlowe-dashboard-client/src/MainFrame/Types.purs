module MainFrame.Types
  ( State
  , PickupState
  , PickupScreen(..)
  , PickupCard(..)
  , WalletState
  , Screen(..)
  , Card(..)
  , ContractStatus(..)
  , ChildSlots
  , Query(..)
  , Msg(..)
  , Action(..)
  , WebSocketStatus(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Contract.Types as Contract
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Marlowe.Semantics (Contract, PubKey)
import Plutus.PAB.Webserver.Types (StreamToClient, StreamToServer)
import Template.Types (Template)
import WalletData.Types (WalletDetails, WalletLibrary, WalletNicknameKey)
import Web.Socket.Event.CloseEvent (CloseEvent, reason) as WS
import WebSocket.Support (FromSocket) as WS

-- Apart from the wallet library (which you need in both cases), the app exists
-- in one of two distinct states: the "pickup" state for when you have no
-- wallet, and all you can do is pick one up or generate a new one; and the
-- "wallet" state for when you have picked up a wallet, and can do all
-- of the things.
type State
  = { wallets :: WalletLibrary
    , newWalletNicknameKey :: WalletNicknameKey
    , templates :: Array Template
    , subState :: Either PickupState WalletState
    -- TODO: (work out how to) move contract state into wallet state
    -- (the puzzle is how to handle contract actions in the mainframe if the
    -- submodule state is behind an `Either`... :thinking_face:)
    , contractState :: Contract.State
    , webSocketStatus :: WebSocketStatus
    }

data WebSocketStatus
  = WebSocketOpen
  | WebSocketClosed (Maybe WS.CloseEvent)

derive instance genericWebSocketStatus :: Generic WebSocketStatus _

instance showWebSocketStatus :: Show WebSocketStatus where
  show WebSocketOpen = "WebSocketOpen"
  show (WebSocketClosed Nothing) = "WebSocketClosed"
  show (WebSocketClosed (Just closeEvent)) = "WebSocketClosed " <> WS.reason closeEvent

type PickupState
  = { screen :: PickupScreen
    , card :: Maybe PickupCard
    }

-- there's only one pickup screen at the moment, but we might need more, and
-- in any case it seems clearer to specify it explicitly
data PickupScreen
  = GenerateWalletScreen

derive instance eqPickupScreen :: Eq PickupScreen

data PickupCard
  = PickupNewWalletCard
  | PickupWalletCard WalletNicknameKey

derive instance eqPickupCard :: Eq PickupCard

type WalletState
  = { wallet :: PubKey
    , menuOpen :: Boolean
    , screen :: Screen
    , card :: Maybe Card
    }

data Screen
  = ContractsScreen ContractStatus
  | WalletLibraryScreen
  | ContractSetupScreen Template

derive instance eqScreen :: Eq Screen

data Card
  = CreateWalletCard
  | ViewWalletCard WalletNicknameKey WalletDetails
  | PutdownWalletCard
  | TemplateLibraryCard
  | ContractCard Contract

derive instance eqCard :: Eq Card

data ContractStatus
  = Running
  | Completed

derive instance eqContractStatus :: Eq ContractStatus

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
  -- pickup actions
  | SetPickupCard (Maybe PickupCard)
  | GenerateNewWallet
  | PickupNewWallet
  | LookupWallet String
  | PickupWallet PubKey
  -- wallet actions
  | PutdownWallet
  | ToggleMenu
  | SetScreen Screen
  | SetCard (Maybe Card)
  | ToggleCard Card
  | SetNewWalletNickname String
  | SetNewWalletKey PubKey
  | AddNewWallet
  -- contract actions
  | ContractAction Contract.Action
  | StartContract Contract

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  -- pickup actions
  toEvent (SetPickupCard _) = Just $ defaultEvent "SetPickupCard"
  toEvent GenerateNewWallet = Just $ defaultEvent "GenerateNewWallet"
  toEvent PickupNewWallet = Just $ defaultEvent "PickupNewWallet"
  toEvent (LookupWallet _) = Nothing
  toEvent (PickupWallet _) = Just $ defaultEvent "PickupWallet"
  -- wallet actions
  toEvent PutdownWallet = Just $ defaultEvent "PutdownWallet"
  toEvent ToggleMenu = Just $ defaultEvent "ToggleMenu"
  toEvent (SetScreen _) = Just $ defaultEvent "SetScreen"
  toEvent (SetCard _) = Just $ defaultEvent "SetCard"
  toEvent (ToggleCard _) = Just $ defaultEvent "ToggleCard"
  toEvent (SetNewWalletNickname _) = Nothing
  toEvent (SetNewWalletKey _) = Nothing
  toEvent AddNewWallet = Just $ defaultEvent "AddNewWallet"
  -- contract actions
  toEvent (ContractAction contractAction) = toEvent contractAction
  toEvent (StartContract _) = Just $ defaultEvent "StartContract"
