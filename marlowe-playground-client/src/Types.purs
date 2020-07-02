module Types where

import API (RunResult)
import Analytics (class IsEvent, defaultEvent)
import Blockly.Types (BlocklyState)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Json.JsonEither (JsonEither)
import Data.Lens (Lens', (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Halogen (ClassName(..))
import Halogen as H
import Halogen.Blockly (BlocklyMessage, BlocklyQuery)
import Halogen.Classes (activeClass)
import Halogen.Monaco (KeyBindings)
import Halogen.Monaco as Monaco
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult)
import Network.RemoteData (RemoteData)
import Prelude (class Eq, class Show, Unit, eq, show, (<<<), ($))
import Servant.PureScript.Ajax (AjaxError)
import Simulation.Types as Simulation
import Wallet as Wallet

------------------------------------------------------------
data HQuery a
  = ReceiveWebsocketMessage String a

data Message
  = WebsocketMessage String

data HAction
  -- Haskell Editor
  = HaskellHandleEditorMessage Monaco.Message
  | HaskellSelectEditorKeyBindings KeyBindings
  | ShowBottomPanel Boolean
  -- haskell actions
  | CompileHaskellProgram
  | ChangeView View
  | SendResultToSimulator
  | SendResultToBlockly
  | LoadHaskellScript String
  -- Simulation Actions
  | HandleSimulationMessage Simulation.Message
  -- blockly
  | HandleBlocklyMessage BlocklyMessage
  -- Wallet Actions
  | HandleWalletMessage Wallet.Message

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent HAction where
  toEvent (HaskellHandleEditorMessage _) = Just $ defaultEvent "HaskellHandleEditorMessage"
  toEvent (HaskellSelectEditorKeyBindings _) = Just $ defaultEvent "HaskellSelectEditorKeyBindings"
  toEvent (HandleSimulationMessage action) = Just $ defaultEvent "HandleSimulationMessage"
  toEvent (HandleWalletMessage action) = Just $ defaultEvent "HandleWalletMessage"
  toEvent CompileHaskellProgram = Just $ defaultEvent "CompileHaskellProgram"
  toEvent (ChangeView view) = Just $ (defaultEvent "View") { label = Just (show view) }
  toEvent (LoadHaskellScript script) = Just $ (defaultEvent "LoadScript") { label = Just script }
  toEvent (HandleBlocklyMessage _) = Just $ (defaultEvent "HandleBlocklyMessage") { category = Just "Blockly" }
  toEvent (ShowBottomPanel _) = Just $ defaultEvent "ShowBottomPanel"
  toEvent SendResultToSimulator = Just $ defaultEvent "SendResultToSimulator"
  toEvent SendResultToBlockly = Just $ defaultEvent "SendResultToBlockly"

------------------------------------------------------------
type ChildSlots
  = ( haskellEditorSlot :: H.Slot Monaco.Query Monaco.Message Unit
    , blocklySlot :: H.Slot BlocklyQuery BlocklyMessage Unit
    , simulationSlot :: H.Slot Simulation.Query Simulation.Message Unit
    , walletSlot :: H.Slot Wallet.Query Wallet.Message Unit
    )

_haskellEditorSlot :: SProxy "haskellEditorSlot"
_haskellEditorSlot = SProxy

_blocklySlot :: SProxy "blocklySlot"
_blocklySlot = SProxy

_simulationSlot :: SProxy "simulationSlot"
_simulationSlot = SProxy

_walletSlot :: SProxy "walletSlot"
_walletSlot = SProxy

-----------------------------------------------------------
data View
  = HaskellEditor
  | Simulation
  | BlocklyEditor
  | WalletEmulator

derive instance eqView :: Eq View

derive instance genericView :: Generic View _

instance showView :: Show View where
  show = genericShow

newtype FrontendState
  = FrontendState
  { view :: View
  , compilationResult :: WebData (JsonEither InterpreterError (InterpreterResult RunResult))
  , blocklyState :: Maybe BlocklyState
  , haskellEditorKeybindings :: KeyBindings
  , activeHaskellDemo :: String
  , showBottomPanel :: Boolean
  }

derive instance newtypeFrontendState :: Newtype FrontendState _

type WebData
  = RemoteData AjaxError

data MarloweError
  = MarloweError String

_view :: Lens' FrontendState View
_view = _Newtype <<< prop (SProxy :: SProxy "view")

_compilationResult :: Lens' FrontendState (WebData (JsonEither InterpreterError (InterpreterResult RunResult)))
_compilationResult = _Newtype <<< prop (SProxy :: SProxy "compilationResult")

_blocklyState :: Lens' FrontendState (Maybe BlocklyState)
_blocklyState = _Newtype <<< prop (SProxy :: SProxy "blocklyState")

_haskellEditorKeybindings :: Lens' FrontendState KeyBindings
_haskellEditorKeybindings = _Newtype <<< prop (SProxy :: SProxy "haskellEditorKeybindings")

_activeHaskellDemo :: Lens' FrontendState String
_activeHaskellDemo = _Newtype <<< prop (SProxy :: SProxy "activeHaskellDemo")

_showBottomPanel :: Lens' FrontendState Boolean
_showBottomPanel = _Newtype <<< prop (SProxy :: SProxy "showBottomPanel")

-- editable
_timestamp ::
  forall s a.
  Lens' { timestamp :: a | s } a
_timestamp = prop (SProxy :: SProxy "timestamp")

_value :: forall s a. Lens' { value :: a | s } a
_value = prop (SProxy :: SProxy "value")

isActiveTab :: FrontendState -> View -> Array ClassName
isActiveTab state activeView = state ^. _view <<< (activeClass (eq activeView))

analysisPanel :: FrontendState -> Array ClassName
analysisPanel state = if state ^. _showBottomPanel then [ ClassName "analysis-panel" ] else [ ClassName "analysis-panel", ClassName "collapse" ]

footerPanelBg :: Boolean -> View -> Array ClassName
footerPanelBg display HaskellEditor =
  if display then
    [ ClassName "footer-panel-bg", ClassName "expanded", ClassName "footer-panel-haskell" ]
  else
    [ ClassName "footer-panel-bg", ClassName "footer-panel-haskell" ]

footerPanelBg display _ =
  if display then
    [ ClassName "footer-panel-bg", ClassName "expanded" ]
  else
    [ ClassName "footer-panel-bg" ]
