module Types where

import Analytics (class IsEvent, defaultEvent, toEvent)
import Blockly.Types (BlocklyState)
import Data.Either (Either)
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
import Halogen.ActusBlockly as AB
import Halogen.Blockly (BlocklyMessage, BlocklyQuery)
import Halogen.Classes (activeClass)
import Halogen.HTML (IProp, attr)
import Halogen.Monaco (KeyBindings)
import Halogen.Monaco as Monaco
import HaskellEditor.Types as HE
import Language.Javascript.Interpreter as JS
import Marlowe.Semantics (Contract)
import Network.RemoteData (RemoteData)
import NewProject.Types as NewProject
import Prelude (class Eq, class Show, Unit, eq, show, (<<<), ($))
import Projects.Types as Projects
import Router (Route)
import Servant.PureScript.Ajax (AjaxError)
import Simulation.Types as Simulation
import Wallet as Wallet

------------------------------------------------------------
data HQuery a
  = ChangeRoute Route a

data HAction
  = Init
  -- Home Page
  | ShowHomePageInFuture Boolean
  -- Haskell Editor
  | HaskellAction HE.Action
  | SimulationAction Simulation.Action
  | JSHandleEditorMessage Monaco.Message
  | JSSelectEditorKeyBindings KeyBindings
  | ShowBottomPanel Boolean
  -- haskell actions
  | CompileJSProgram
  | CompiledJSProgram (Either JS.CompilationError (JS.InterpreterResult Contract))
  | ChangeView View
  | SendResultJSToSimulator
  | LoadJSScript String
  -- blockly
  | HandleBlocklyMessage BlocklyMessage
  | HandleActusBlocklyMessage AB.BlocklyMessage
  -- Wallet Actions
  | HandleWalletMessage Wallet.Message
  | ProjectsAction Projects.Action
  | NewProjectAction NewProject.Action

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent HAction where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (ShowHomePageInFuture b) = Just $ (defaultEvent "ShowHomePageInFuture") { label = Just (show b) }
  toEvent (HaskellAction action) = toEvent action
  toEvent (JSHandleEditorMessage _) = Just $ defaultEvent "JSHandleEditorMessage"
  toEvent (SimulationAction action) = toEvent action
  toEvent (JSSelectEditorKeyBindings _) = Just $ defaultEvent "JSSelectEditorKeyBindings"
  toEvent (HandleWalletMessage action) = Just $ defaultEvent "HandleWalletMessage"
  toEvent CompileJSProgram = Just $ defaultEvent "CompileJSProgram"
  toEvent (CompiledJSProgram _) = Just $ defaultEvent "CompiledJSProgram"
  toEvent (ChangeView view) = Just $ (defaultEvent "View") { label = Just (show view) }
  toEvent (LoadJSScript script) = Just $ (defaultEvent "LoadJSScript") { label = Just script }
  toEvent (HandleBlocklyMessage _) = Just $ (defaultEvent "HandleBlocklyMessage") { category = Just "Blockly" }
  toEvent (HandleActusBlocklyMessage _) = Just $ (defaultEvent "HandleActusBlocklyMessage") { category = Just "ActusBlockly" }
  toEvent (ShowBottomPanel _) = Just $ defaultEvent "ShowBottomPanel"
  toEvent SendResultJSToSimulator = Just $ defaultEvent "SendResultJSToSimulator"
  toEvent (ProjectsAction action) = toEvent action
  toEvent (NewProjectAction action) = toEvent action

------------------------------------------------------------
type ChildSlots
  = ( haskellEditorSlot :: H.Slot Monaco.Query Monaco.Message Unit
    , jsEditorSlot :: H.Slot Monaco.Query Monaco.Message Unit
    , blocklySlot :: H.Slot BlocklyQuery BlocklyMessage Unit
    , actusBlocklySlot :: H.Slot AB.BlocklyQuery AB.BlocklyMessage Unit
    , simulationSlot :: H.Slot Simulation.Query BlocklyMessage Unit
    , marloweEditorSlot :: H.Slot Monaco.Query Monaco.Message Unit
    , walletSlot :: H.Slot Wallet.Query Wallet.Message Unit
    )

_haskellEditorSlot :: SProxy "haskellEditorSlot"
_haskellEditorSlot = SProxy

_jsEditorSlot :: SProxy "jsEditorSlot"
_jsEditorSlot = SProxy

_blocklySlot :: SProxy "blocklySlot"
_blocklySlot = SProxy

_actusBlocklySlot :: SProxy "actusBlocklySlot"
_actusBlocklySlot = SProxy

_simulationSlot :: SProxy "simulationSlot"
_simulationSlot = SProxy

_marloweEditorSlot :: SProxy "marloweEditorSlot"
_marloweEditorSlot = SProxy

_walletSlot :: SProxy "walletSlot"
_walletSlot = SProxy

-----------------------------------------------------------
data View
  = HomePage
  | HaskellEditor
  | JSEditor
  | Simulation
  | BlocklyEditor
  | ActusBlocklyEditor
  | WalletEmulator
  | Projects
  | NewProject

derive instance eqView :: Eq View

derive instance genericView :: Generic View _

instance showView :: Show View where
  show = genericShow

data JSCompilationState
  = JSNotCompiled
  | JSCompiling
  | JSCompilationError JS.CompilationError
  | JSCompiledSuccessfully (JS.InterpreterResult Contract)

newtype FrontendState
  = FrontendState
  { view :: View
  , jsCompilationResult :: JSCompilationState
  , blocklyState :: Maybe BlocklyState
  , actusBlocklyState :: Maybe BlocklyState
  , jsEditorKeybindings :: KeyBindings
  , activeJSDemo :: String
  , showBottomPanel :: Boolean
  , haskellState :: HE.State
  , simulationState :: Simulation.State
  , showHomePage :: Boolean
  , projects :: Projects.State
  , newProject :: NewProject.State
  }

derive instance newtypeFrontendState :: Newtype FrontendState _

type WebData
  = RemoteData AjaxError

data MarloweError
  = MarloweError String

_view :: Lens' FrontendState View
_view = _Newtype <<< prop (SProxy :: SProxy "view")

_jsCompilationResult :: Lens' FrontendState JSCompilationState
_jsCompilationResult = _Newtype <<< prop (SProxy :: SProxy "jsCompilationResult")

_blocklyState :: Lens' FrontendState (Maybe BlocklyState)
_blocklyState = _Newtype <<< prop (SProxy :: SProxy "blocklyState")

_actusBlocklyState :: Lens' FrontendState (Maybe BlocklyState)
_actusBlocklyState = _Newtype <<< prop (SProxy :: SProxy "actusBlocklyState")

_jsEditorKeybindings :: Lens' FrontendState KeyBindings
_jsEditorKeybindings = _Newtype <<< prop (SProxy :: SProxy "jsEditorKeybindings")

_activeJSDemo :: Lens' FrontendState String
_activeJSDemo = _Newtype <<< prop (SProxy :: SProxy "activeJSDemo")

_showBottomPanel :: Lens' FrontendState Boolean
_showBottomPanel = _Newtype <<< prop (SProxy :: SProxy "showBottomPanel")

_haskellState :: Lens' FrontendState HE.State
_haskellState = _Newtype <<< prop (SProxy :: SProxy "haskellState")

_simulationState :: Lens' FrontendState Simulation.State
_simulationState = _Newtype <<< prop (SProxy :: SProxy "simulationState")

_showHomePage :: Lens' FrontendState Boolean
_showHomePage = _Newtype <<< prop (SProxy :: SProxy "showHomePage")

_projects :: Lens' FrontendState Projects.State
_projects = _Newtype <<< prop (SProxy :: SProxy "projects")

_newProject :: Lens' FrontendState NewProject.State
_newProject = _Newtype <<< prop (SProxy :: SProxy "newProject")

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
