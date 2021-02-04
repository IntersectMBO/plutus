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
  | ToggleOverlay Overlay
  | SetScreen Screen
  | ToggleCard Card
  | CloseCard
  | ClickedButton

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (ToggleOverlay _) = Just $ defaultEvent "ToggleOverlay"
  toEvent (SetScreen _) = Just $ defaultEvent "SetFrame"
  toEvent (ToggleCard _) = Just $ defaultEvent "ToggleCard"
  toEvent CloseCard = Just $ defaultEvent "CloseCard"
  toEvent ClickedButton = Just $ defaultEvent "ClickedButton"

type ChildSlots
  = (
    )

type State
  = { overlay :: Maybe Overlay
    , screen :: Screen
    , card :: Maybe Card
    , notifications :: Array Notification
    , templates :: Array ContractTemplate
    , contracts :: Array Contract
    , on :: Boolean
    }

data Overlay
  = Menu
  | Notifications

derive instance eqOverlay :: Eq Overlay

data Screen
  = Home
  | Contracts
  | SetupContract ContractTemplate

derive instance eqFrame :: Eq Screen

data Card
  = TemplateLibrary
  | TemplateDetails ContractTemplate
  | ContractDetails Contract

derive instance eqCard :: Eq Card

-- notification type TBD
type Notification
  = Int

-- contract template type TBD
type ContractTemplate
  = Int

-- TODO: move Marlowe.Semantics into web-common-marlowe and get Contract type from there
type Contract
  = Int
