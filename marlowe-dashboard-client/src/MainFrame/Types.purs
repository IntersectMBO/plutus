module MainFrame.Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import WebSocket (StreamToClient, StreamToServer)
import WebSocket.Support as WS

data Query a
  = ReceiveWebSocketMessage (WS.FromSocket StreamToClient) a

data Msg
  = SendWebSocketMessage StreamToServer

data Action
  = Init
  | ClickedButton

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent ClickedButton = Just $ defaultEvent "ClickedButton"

type ChildSlots
  = (
    )

type State
  = { on :: Boolean
    }

_on :: Lens' State Boolean
_on = prop (SProxy :: SProxy "on")
