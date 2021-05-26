-- A separate module for types that are shared between Simulation and Simulation.BottomPanel
module SimulationPage.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import BottomPanel.Types as BottomPanel
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.List.Types (NonEmptyList)
import Data.Maybe (Maybe(..))
import Help (HelpContext)
import Marlowe.Extended (IntegerTemplateType)
import Marlowe.Semantics (Bound, ChoiceId, ChosenNum, Input, Slot)
import Marlowe.Symbolic.Types.Response (Result)
import Network.RemoteData (RemoteData)
import Simulator.Types (MarloweState)

--
type State
  = { showRightPanel :: Boolean
    , bottomPanelState :: BottomPanel.State BottomPanelView
    , marloweState :: NonEmptyList MarloweState
    , helpContext :: HelpContext
    }

data Action
  = Init
  -- marlowe actions
  | SetInitialSlot Slot
  | SetIntegerTemplateParam IntegerTemplateType String BigInteger
  | StartSimulation
  | MoveSlot Slot
  | SetSlot Slot
  | AddInput Input (Array Bound)
  | SetChoice ChoiceId ChosenNum
  | ResetSimulator
  | Undo
  | LoadContract String
  -- simulation view
  -- FIXME: We are not showing a help context. See if we want to bring back this
  --       functionality or delete this code
  | ChangeHelpContext HelpContext
  -- FIXME: This action is not triggerable at the moment. Check if we want to bring
  --        back this functionality or delete this code
  | ShowRightPanel Boolean
  | BottomPanelAction (BottomPanel.Action BottomPanelView Action)
  | EditSource

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "Simulation." <> s

instance isEventAction :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (SetInitialSlot _) = Just $ defaultEvent "SetInitialSlot"
  toEvent (SetIntegerTemplateParam templateType key value) = Just $ defaultEvent "SetIntegerTemplateParam"
  toEvent StartSimulation = Just $ defaultEvent "StartSimulation"
  toEvent (MoveSlot _) = Just $ defaultEvent "MoveSlot"
  toEvent (SetSlot _) = Just $ defaultEvent "SetSlot"
  toEvent (AddInput _ _) = Just $ defaultEvent "AddInput"
  toEvent (SetChoice _ _) = Just $ defaultEvent "SetChoice"
  toEvent ResetSimulator = Just $ defaultEvent "ResetSimulator"
  toEvent Undo = Just $ defaultEvent "Undo"
  toEvent (LoadContract _) = Just $ defaultEvent "LoadContract"
  toEvent (ChangeHelpContext help) = Just $ (defaultEvent "ChangeHelpContext") { label = Just $ show help }
  toEvent (ShowRightPanel _) = Just $ defaultEvent "ShowRightPanel"
  toEvent (BottomPanelAction action) = A.toEvent action
  toEvent EditSource = Just $ defaultEvent "EditSource"

data Query a
  = WebsocketResponse (RemoteData String Result) a

data BottomPanelView
  = CurrentStateView

derive instance eqBottomPanelView :: Eq BottomPanelView

derive instance genericBottomPanelView :: Generic BottomPanelView _

instance showBottomPanelView :: Show BottomPanelView where
  show = genericShow
