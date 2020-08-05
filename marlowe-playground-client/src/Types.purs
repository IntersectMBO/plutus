module Types where

import Analytics (class IsEvent, defaultEvent, toEvent)
import Blockly.Types (BlocklyState)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens', (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Halogen (AttrName(..), ClassName)
import Halogen as H
import Halogen.Blockly (BlocklyMessage, BlocklyQuery)
import Halogen.Classes (activeClass)
import Halogen.HTML (IProp, attr)
import Halogen.Monaco as Monaco
import HaskellEditor.Types as HE
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
  = HaskellAction HE.Action
  | ShowBottomPanel Boolean
  -- haskell actions
  | ChangeView View
  -- Simulation Actions
  | HandleSimulationMessage Simulation.Message
  -- blockly
  | HandleBlocklyMessage BlocklyMessage
  -- Wallet Actions
  | HandleWalletMessage Wallet.Message

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent HAction where
  toEvent (HaskellAction action) = toEvent action
  toEvent (HandleSimulationMessage action) = Just $ defaultEvent "HandleSimulationMessage"
  toEvent (HandleWalletMessage action) = Just $ defaultEvent "HandleWalletMessage"
  toEvent (ChangeView view) = Just $ (defaultEvent "View") { label = Just (show view) }
  toEvent (HandleBlocklyMessage _) = Just $ (defaultEvent "HandleBlocklyMessage") { category = Just "Blockly" }
  toEvent (ShowBottomPanel _) = Just $ defaultEvent "ShowBottomPanel"

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
  , blocklyState :: Maybe BlocklyState
  , showBottomPanel :: Boolean
  , haskellState :: HE.State
  }

derive instance newtypeFrontendState :: Newtype FrontendState _

type WebData
  = RemoteData AjaxError

data MarloweError
  = MarloweError String

_view :: Lens' FrontendState View
_view = _Newtype <<< prop (SProxy :: SProxy "view")

_blocklyState :: Lens' FrontendState (Maybe BlocklyState)
_blocklyState = _Newtype <<< prop (SProxy :: SProxy "blocklyState")

_showBottomPanel :: Lens' FrontendState Boolean
_showBottomPanel = _Newtype <<< prop (SProxy :: SProxy "showBottomPanel")

_haskellState :: Lens' FrontendState HE.State
_haskellState = _Newtype <<< prop (SProxy :: SProxy "haskellState")

-- editable
_timestamp ::
  forall s a.
  Lens' { timestamp :: a | s } a
_timestamp = prop (SProxy :: SProxy "timestamp")

_value :: forall s a. Lens' { value :: a | s } a
_value = prop (SProxy :: SProxy "value")

isActiveTab :: FrontendState -> View -> Array ClassName
isActiveTab state activeView = state ^. _view <<< (activeClass (eq activeView))

-- TODO: https://github.com/purescript-halogen/purescript-halogen/issues/682
bottomPanelHeight :: forall r i. Boolean -> IProp r i
bottomPanelHeight true = attr (AttrName "style") ""

bottomPanelHeight false = attr (AttrName "style") "height: 3.5rem"
