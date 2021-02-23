module BlocklyEditor.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import BlocklyComponent.Types as Blockly
import BottomPanel.Types as BottomPanel
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Symbol (SProxy(..))
import Marlowe.Linter (Warning)
import Marlowe.Extended (IntegerTemplateType)
import StaticAnalysis.Types (AnalysisState, initAnalysisState)

data Action
  = Init
  | HandleBlocklyMessage Blockly.Message
  | InitBlocklyProject String
  | SendToSimulator
  | ViewAsMarlowe
  | Save
  | BottomPanelAction (BottomPanel.Action BottomPanelView Action)
  | AnalyseContract
  | AnalyseReachabilityContract
  | AnalyseContractForCloseRefund
  | SetIntegerTemplateParam IntegerTemplateType String BigInteger
  | ClearAnalysisResults
  | SelectWarning Warning
  | ResizeWorkspace

defaultEvent :: String -> Event
defaultEvent s = (A.defaultEvent $ "BlocklyEditor." <> s) { category = Just "Blockly" }

instance blocklyActionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (HandleBlocklyMessage _) = Just $ defaultEvent "HandleBlocklyMessage"
  toEvent (InitBlocklyProject _) = Just $ defaultEvent "InitBlocklyProject"
  toEvent SendToSimulator = Just $ defaultEvent "SendToSimulator"
  toEvent ViewAsMarlowe = Just $ defaultEvent "ViewAsMarlowe"
  toEvent Save = Just $ defaultEvent "Save"
  toEvent (BottomPanelAction action) = A.toEvent action
  toEvent AnalyseContract = Just $ defaultEvent "AnalyseContract"
  toEvent AnalyseReachabilityContract = Just $ defaultEvent "AnalyseReachabilityContract"
  toEvent AnalyseContractForCloseRefund = Just $ defaultEvent "AnalyseContractForCloseRefund"
  toEvent (SetIntegerTemplateParam _ _ _) = Just $ defaultEvent "SetIntegerTemplateParam"
  toEvent ClearAnalysisResults = Just $ defaultEvent "ClearAnalysisResults"
  toEvent (SelectWarning _) = Just $ defaultEvent "SelectWarning"
  toEvent ResizeWorkspace = Just $ defaultEvent "ResizeWorkspace"

data BottomPanelView
  = StaticAnalysisView
  | BlocklyWarningsView

derive instance eqBottomPanelView :: Eq BottomPanelView

derive instance genericBottomPanelView :: Generic BottomPanelView _

instance showBottomPanelView :: Show BottomPanelView where
  show = genericShow

type State
  = { errorMessage :: Maybe String
    , marloweCode :: Maybe String
    , hasHoles :: Boolean
    , bottomPanelState :: BottomPanel.State BottomPanelView
    , analysisState :: AnalysisState
    , warnings :: Array Warning
    }

_errorMessage :: Lens' State (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

_marloweCode :: Lens' State (Maybe String)
_marloweCode = prop (SProxy :: SProxy "marloweCode")

_hasHoles :: Lens' State Boolean
_hasHoles = prop (SProxy :: SProxy "hasHoles")

_bottomPanelState :: Lens' State (BottomPanel.State BottomPanelView)
_bottomPanelState = prop (SProxy :: SProxy "bottomPanelState")

_warnings :: Lens' State (Array Warning)
_warnings = prop (SProxy :: SProxy "warnings")

initialState :: State
initialState =
  { errorMessage: Nothing
  , marloweCode: Nothing
  , hasHoles: false
  , bottomPanelState: BottomPanel.initialState StaticAnalysisView
  , analysisState: initAnalysisState
  , warnings: mempty
  }
