module MainFrame.Types
  ( State
  , WebSocketStatus(..)
  , ChildSlots
  , Query(..)
  , Msg(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Contract.Types (State) as Contract
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Marlowe.PAB (PlutusAppId, CombinedWSStreamToServer)
import Pickup.Types (Action, State) as Pickup
import Play.Types (Action, State) as Play
import Plutus.PAB.Webserver.Types (CombinedWSStreamToClient)
--import Plutus.PAB.Webserver.Types (CombinedWSStreamToClient, CombinedWSStreamToServer)
import Toast.Types (Action, State) as Toast
import WalletData.Types (WalletDetails, WalletLibrary)
import Web.Socket.Event.CloseEvent (CloseEvent, reason) as WS
import WebSocket.Support (FromSocket) as WS

-- The app exists in one of two main subStates: the "pickup" state for when you have
-- no wallet, and all you can do is pick one up or generate a new one; and the "play"
-- state for when you have picked up a wallet, and can do all of the things.
type State
  = { webSocketStatus :: WebSocketStatus
    , subState :: Either Pickup.State Play.State
    , toast :: Toast.State
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
  = ReceiveWebSocketMessage (WS.FromSocket CombinedWSStreamToClient) a
  | MainFrameActionQuery Action a

data Msg
  = SendWebSocketMessage CombinedWSStreamToServer
  | MainFrameActionMsg Action

------------------------------------------------------------
data Action
  = Init
  | EnterPickupState WalletLibrary WalletDetails (Map PlutusAppId Contract.State)
  | EnterPlayState WalletLibrary WalletDetails
  | PickupAction Pickup.Action
  | PlayAction Play.Action
  | ToastAction Toast.Action

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (EnterPickupState _ _ _) = Just $ defaultEvent "EnterPickupState"
  toEvent (EnterPlayState _ _) = Just $ defaultEvent "EnterPlayState"
  toEvent (PickupAction pickupAction) = toEvent pickupAction
  toEvent (PlayAction playAction) = toEvent playAction
  toEvent (ToastAction toastAction) = toEvent toastAction
