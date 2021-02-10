module MainFrame.Types
  ( State(..)
  , Overlay(..)
  , Screen(..)
  , Card(..)
  , Notification
  , ContractTemplate
  , ContractInstance
  , ContractStatus(..)
  , ChildSlots
  , Query(..)
  , Msg(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Contact.Types (Action, ContactKey, State) as Contact
import Data.Maybe (Maybe(..))
import WebSocket (StreamToClient, StreamToServer)
import WebSocket.Support as WS

type State
  = { overlay :: Maybe Overlay
    , screen :: Screen
    , card :: Maybe Card
    , contactState :: Contact.State
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
  | SetupContract ContractTemplate
  | ViewContract ContractInstance

derive instance eqFrame :: Eq Screen

data Card
  = NewContact
  | EditContact Contact.ContactKey
  | TemplateLibrary
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
  | ToggleOverlay Overlay
  | SetScreen Screen
  | ToggleCard Card
  | CloseCard
  | ContactAction Contact.Action
  | ClickedButton

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (ToggleOverlay _) = Just $ defaultEvent "ToggleOverlay"
  toEvent (SetScreen _) = Just $ defaultEvent "SetFrame"
  toEvent (ToggleCard _) = Just $ defaultEvent "ToggleCard"
  toEvent CloseCard = Just $ defaultEvent "CloseCard"
  toEvent (ContactAction contactAction) = toEvent contactAction
  toEvent ClickedButton = Just $ defaultEvent "ClickedButton"
