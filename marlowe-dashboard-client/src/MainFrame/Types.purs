module MainFrame.Types
  ( State
  , ChildSlots
  , Query(..)
  , Msg(..)
  , Action(..)
  , WebSocketStatus(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Play.Types (Action, State) as Play
import Plutus.PAB.Webserver.Types (StreamToClient, StreamToServer)
import Pickup.Types (Action, State) as Pickup
import Template.Types (Template)
import WalletData.Types (WalletLibrary, WalletNicknameKey)
import Web.Socket.Event.CloseEvent (CloseEvent, reason) as WS
import WebSocket.Support (FromSocket) as WS

-- Apart from the wallet library (which you need in both cases), the app exists
-- in one of two distinct states: the "pickup" state for when you have no wallet,
-- and all you can do is pick one up or generate a new one; and the "play" state
-- for when you have picked up a wallet, and can do all of the things.
type State
  = { wallets :: WalletLibrary
    , newWalletNicknameKey :: WalletNicknameKey
    , templates :: Array Template
    , webSocketStatus :: WebSocketStatus
    , subState :: Either Pickup.State Play.State
    }

data WebSocketStatus
  = WebSocketOpen
  | WebSocketClosed (Maybe WS.CloseEvent)

derive instance genericWebSocketStatus :: Generic WebSocketStatus _

instance showWebSocketStatus :: Show WebSocketStatus where
  show WebSocketOpen = "WebSocketOpen"
  show (WebSocketClosed Nothing) = "WebSocketClosed"
  show (WebSocketClosed (Just closeEvent)) = "WebSocketClosed " <> WS.reason closeEvent

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
  | SetNewWalletNickname String
  | AddNewWallet
  | PickupAction Pickup.Action
  | PlayAction Play.Action

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (SetNewWalletNickname _) = Nothing
  toEvent AddNewWallet = Just $ defaultEvent "AddNewWallet"
  toEvent (PickupAction pickupAction) = toEvent pickupAction
  toEvent (PlayAction playAction) = toEvent playAction
