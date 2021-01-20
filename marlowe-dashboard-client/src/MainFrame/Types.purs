module MainFrame.Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Maybe (Maybe(..))
import WebSocket (StreamToClient, StreamToServer)
import WebSocket.Support as WS

data Query a
  = ReceiveWebSocketMessage (WS.FromSocket StreamToClient) a

data Msg
  = SendWebSocketMessage StreamToServer

data Action
  = Init

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"

type ChildSlots
  = (
    )

type State
  = {
    }
