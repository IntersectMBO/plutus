module MainFrame.Types where

import Analytics (class IsEvent, defaultEvent, toEvent)
import Auth (AuthStatus)
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
import Demos.Types as Demos
import Gist (Gist, GistId)
import Gists (GistAction)
import Halogen (ClassName)
import Halogen as H
import Halogen.ActusBlockly as AB
import Halogen.Blockly as Blockly
import Halogen.Classes (activeClass)
import Halogen.Monaco (KeyBindings)
import Halogen.Monaco as Monaco
import HaskellEditor.Types as HE
import JavascriptEditor.Types (CompilationState)
import JavascriptEditor.Types as JS
import NewProject.Types as NewProject
import Prelude (class Eq, class Show, Unit, eq, show, (<<<), ($))
import Projects.Types as Projects
import Rename.Types as Rename
import Router (Route)
import SaveAs.Types as SaveAs
import Simulation.Types as Simulation
import Types (WebData)
import Wallet as Wallet
import Web.UIEvent.KeyboardEvent (KeyboardEvent)

data ModalView
  = NewProject
  | OpenProject
  | OpenDemo
  | RenameProject
  | SaveProjectAs
  | GithubLogin Action

derive instance genericModalView :: Generic ModalView _

instance showModalView :: Show ModalView where
  show NewProject = "NewProject"
  show OpenProject = "OpenProject"
  show OpenDemo = "OpenDemo"
  show RenameProject = "RenameProject"
  show SaveProjectAs = "SaveProjectAs"
  show (GithubLogin _) = "GithubLogin"
  -- Before adding the intended action to GithubLogin, this instance was being
  -- handled by the genericShow. Action does not have a show instance so genericShow
  -- does not work. For the moment I've made a manual instance, but not sure why
  -- ModalView requires show, or if we should make Action an instance of Show
  -- show = genericShow

data Query a
  = ChangeRoute Route a

data Action
  = Init
  | HandleKey H.SubscriptionId KeyboardEvent
  | HaskellAction HE.Action
  | SimulationAction Simulation.Action
  | SendBlocklyToSimulator
  | JavascriptAction JS.Action
  | ShowBottomPanel Boolean
  | ChangeView View
  -- blockly
  | HandleBlocklyMessage Blockly.Message
  | HandleActusBlocklyMessage AB.Message
  -- Wallet Actions
  | HandleWalletMessage Wallet.Message
  | ProjectsAction Projects.Action
  | NewProjectAction NewProject.Action
  | DemosAction Demos.Action
  | RenameAction Rename.Action
  | SaveAsAction SaveAs.Action
  -- Gist support.
  | CheckAuthStatus
  | GistAction GistAction
  | OpenModal ModalView
  | CloseModal
  | ChangeProjectName String
  | OpenLoginPopup Action

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (HandleKey _ _) = Just $ defaultEvent "HandleKey"
  toEvent (HaskellAction action) = toEvent action
  toEvent (SimulationAction action) = toEvent action
  toEvent SendBlocklyToSimulator = Just $ defaultEvent "SendBlocklyToSimulator"
  toEvent (JavascriptAction action) = toEvent action
  toEvent (HandleWalletMessage action) = Just $ defaultEvent "HandleWalletMessage"
  toEvent (ChangeView view) = Just $ (defaultEvent "View") { label = Just (show view) }
  toEvent (HandleBlocklyMessage _) = Just $ (defaultEvent "HandleBlocklyMessage") { category = Just "Blockly" }
  toEvent (HandleActusBlocklyMessage _) = Just $ (defaultEvent "HandleActusBlocklyMessage") { category = Just "ActusBlockly" }
  toEvent (ShowBottomPanel _) = Just $ defaultEvent "ShowBottomPanel"
  toEvent (ProjectsAction action) = toEvent action
  toEvent (NewProjectAction action) = toEvent action
  toEvent (DemosAction action) = toEvent action
  toEvent (RenameAction action) = toEvent action
  toEvent (SaveAsAction action) = toEvent action
  toEvent CheckAuthStatus = Just $ defaultEvent "CheckAuthStatus"
  toEvent (GistAction _) = Just $ defaultEvent "GistAction"
  toEvent (OpenModal view) = Just $ (defaultEvent (show view)) { category = Just "OpenModal" }
  toEvent CloseModal = Just $ defaultEvent "CloseModal"
  toEvent (ChangeProjectName _) = Just $ defaultEvent "ChangeProjectName"
  toEvent (OpenLoginPopup _)  = Just $ defaultEvent "OpenLoginPopup"

data View
  = HomePage
  | HaskellEditor
  | JSEditor
  | Simulation
  | BlocklyEditor
  | ActusBlocklyEditor
  | WalletEmulator

derive instance eqView :: Eq View

derive instance genericView :: Generic View _

instance showView :: Show View where
  show = genericShow

type ChildSlots
  = ( haskellEditorSlot :: H.Slot Monaco.Query Monaco.Message Unit
    , jsEditorSlot :: H.Slot Monaco.Query Monaco.Message Unit
    , blocklySlot :: H.Slot Blockly.Query Blockly.Message Unit
    , actusBlocklySlot :: H.Slot AB.Query AB.Message Unit
    , simulationSlot :: H.Slot Simulation.Query Blockly.Message Unit
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
newtype State
  = State
  { view :: View
  , jsCompilationResult :: CompilationState
  , blocklyState :: Maybe BlocklyState
  , actusBlocklyState :: Maybe BlocklyState
  , jsEditorKeybindings :: KeyBindings
  , activeJSDemo :: String
  , showBottomPanel :: Boolean
  , haskellState :: HE.State
  , javascriptState :: JS.State
  , simulationState :: Simulation.State
  , projects :: Projects.State
  , newProject :: NewProject.State
  , rename :: Rename.State
  , saveAs :: SaveAs.State
  , authStatus :: WebData AuthStatus
  , gistId :: Maybe GistId
  , createGistResult :: WebData Gist
  , loadGistResult :: Either String (WebData Gist)
  , projectName :: String
  , showModal :: Maybe ModalView
  }

derive instance newtypeState :: Newtype State _

_view :: Lens' State View
_view = _Newtype <<< prop (SProxy :: SProxy "view")

_jsCompilationResult :: Lens' State CompilationState
_jsCompilationResult = _Newtype <<< prop (SProxy :: SProxy "jsCompilationResult")

_blocklyState :: Lens' State (Maybe BlocklyState)
_blocklyState = _Newtype <<< prop (SProxy :: SProxy "blocklyState")

_actusBlocklyState :: Lens' State (Maybe BlocklyState)
_actusBlocklyState = _Newtype <<< prop (SProxy :: SProxy "actusBlocklyState")

_jsEditorKeybindings :: Lens' State KeyBindings
_jsEditorKeybindings = _Newtype <<< prop (SProxy :: SProxy "jsEditorKeybindings")

_activeJSDemo :: Lens' State String
_activeJSDemo = _Newtype <<< prop (SProxy :: SProxy "activeJSDemo")

_showBottomPanel :: Lens' State Boolean
_showBottomPanel = _Newtype <<< prop (SProxy :: SProxy "showBottomPanel")

_haskellState :: Lens' State HE.State
_haskellState = _Newtype <<< prop (SProxy :: SProxy "haskellState")

_javascriptState :: Lens' State JS.State
_javascriptState = _Newtype <<< prop (SProxy :: SProxy "javascriptState")

_simulationState :: Lens' State Simulation.State
_simulationState = _Newtype <<< prop (SProxy :: SProxy "simulationState")

_projects :: Lens' State Projects.State
_projects = _Newtype <<< prop (SProxy :: SProxy "projects")

_newProject :: Lens' State NewProject.State
_newProject = _Newtype <<< prop (SProxy :: SProxy "newProject")

_rename :: Lens' State Rename.State
_rename = _Newtype <<< prop (SProxy :: SProxy "rename")

_saveAs :: Lens' State SaveAs.State
_saveAs = _Newtype <<< prop (SProxy :: SProxy "saveAs")

_authStatus :: Lens' State (WebData AuthStatus)
_authStatus = _Newtype <<< prop (SProxy :: SProxy "authStatus")

_gistId :: Lens' State (Maybe GistId)
_gistId = _Newtype <<< prop (SProxy :: SProxy "gistId")

_createGistResult :: Lens' State (WebData Gist)
_createGistResult = _Newtype <<< prop (SProxy :: SProxy "createGistResult")

_loadGistResult :: Lens' State (Either String (WebData Gist))
_loadGistResult = _Newtype <<< prop (SProxy :: SProxy "loadGistResult")

_projectName :: Lens' State String
_projectName = _Newtype <<< prop (SProxy :: SProxy "projectName")

_showModal :: Lens' State (Maybe ModalView)
_showModal = _Newtype <<< prop (SProxy :: SProxy "showModal")

-- editable
_timestamp ::
  forall s a.
  Lens' { timestamp :: a | s } a
_timestamp = prop (SProxy :: SProxy "timestamp")

_value :: forall s a. Lens' { value :: a | s } a
_value = prop (SProxy :: SProxy "value")

isActiveTab :: State -> View -> Array ClassName
isActiveTab state activeView = state ^. _view <<< (activeClass (eq activeView))
