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
    , contracts :: Array ContractInstance
    , on :: Boolean
    }

data Overlay
  = Menu
  | Notifications

derive instance eqOverlay :: Eq Overlay

data Screen
  = Home
  | Contacts
  | Contracts ContractStatus
  | SetupContract ContractTemplate

derive instance eqFrame :: Eq Screen

data ContractStatus
  = Running
  | Completed

derive instance eqContractStatus :: Eq ContractStatus

data Card
  = TemplateLibrary
  | TemplateDetails ContractTemplate
  | ContractDetails ContractInstance

derive instance eqCard :: Eq Card

-- notification type TBD
data Notification

-- contract templage type TBD
type ContractTemplate
  = Int

-- contract instance type TBD
type ContractInstance
  = Int
