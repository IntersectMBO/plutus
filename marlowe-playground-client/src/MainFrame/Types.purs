module MainFrame.Types where

import Prelude hiding (div)
import Analytics (class IsEvent, defaultEvent, toEvent)
import Auth (AuthStatus)
import ConfirmUnsavedNavigation.Types as ConfirmUnsavedNavigation
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens', has, (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Demos.Types as Demos
import Gist (Gist, GistId)
import Gists.Types (GistAction)
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
import Network.RemoteData (_Loading)
import MarloweEditor.Types as ME
import NewProject.Types as NewProject
import Projects.Types (Lang(..))
import Projects.Types as Projects
import Rename.Types as Rename
import Router (Route)
import SaveAs.Types as SaveAs
import SimulationPage.Types as Simulation
import Types (WebData)
import WalletSimulation.Types as Wallet
import Web.UIEvent.KeyboardEvent (KeyboardEvent)

data ModalView
  = NewProject
  | OpenProject
  | OpenDemo
  | RenameProject
  | SaveProjectAs
  | GithubLogin Action
  | ConfirmUnsavedNavigation Action

derive instance genericModalView :: Generic ModalView _

instance showModalView :: Show ModalView where
  show NewProject = "NewProject"
  show OpenProject = "OpenProject"
  show OpenDemo = "OpenDemo"
  show RenameProject = "RenameProject"
  show SaveProjectAs = "SaveProjectAs"
  show (ConfirmUnsavedNavigation _) = "ConfirmUnsavedNavigation"
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
  | BlocklyEditorAction BlocklySubAction
  | MarloweEditorAction ME.Action
  | JavascriptAction JS.Action
  | ShowBottomPanel Boolean
  | ChangeView View
  | ConfirmUnsavedNavigationAction Action ConfirmUnsavedNavigation.Action
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
  toEvent (BlocklyEditorAction action) = toEvent action
  toEvent (JavascriptAction action) = toEvent action
  toEvent (MarloweEditorAction action) = toEvent action
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
  toEvent (ConfirmUnsavedNavigationAction _ _) = Just $ defaultEvent "ConfirmUnsavedNavigation"
  toEvent CheckAuthStatus = Just $ defaultEvent "CheckAuthStatus"
  toEvent (GistAction _) = Just $ defaultEvent "GistAction"
  toEvent (OpenModal view) = Just $ (defaultEvent (show view)) { category = Just "OpenModal" }
  toEvent CloseModal = Just $ defaultEvent "CloseModal"
  toEvent (ChangeProjectName _) = Just $ defaultEvent "ChangeProjectName"
  toEvent (OpenLoginPopup _) = Just $ defaultEvent "OpenLoginPopup"

-- TODO: When we change Blockly into a submodule (SCP-1646) this is going to be part of the actions it provides
--       at the moment I put this to refactor "SendBlocklyToSimulator" into SendToSimulator and to
--       add another action
data BlocklySubAction
  = SendToSimulator
  | ViewAsMarlowe

instance blocklyActionIsEvent :: IsEvent BlocklySubAction where
  toEvent SendToSimulator = Just $ (defaultEvent "SendToSimulator") { category = Just "Blockly" }
  toEvent ViewAsMarlowe = Just $ (defaultEvent "ViewAsMarlowe") { category = Just "Blockly" }

data View
  = HomePage
  | MarloweEditor
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
    , simulatorEditorSlot :: H.Slot Monaco.Query Monaco.Message Unit
    , marloweEditorPageSlot :: H.Slot Monaco.Query Monaco.Message Unit
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

_simulatorEditorSlot :: SProxy "simulatorEditorSlot"
_simulatorEditorSlot = SProxy

_marloweEditorPageSlot :: SProxy "marloweEditorPageSlot"
_marloweEditorPageSlot = SProxy

_walletSlot :: SProxy "walletSlot"
_walletSlot = SProxy

-----------------------------------------------------------
newtype State
  = State
  { view :: View
  , jsCompilationResult :: CompilationState
  , jsEditorKeybindings :: KeyBindings
  , activeJSDemo :: String
  , showBottomPanel :: Boolean
  -- TODO: rename to haskellEditorState
  , haskellState :: HE.State
  -- TODO: rename to javascriptEditorState
  , javascriptState :: JS.State
  , marloweEditorState :: ME.State
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
  -- The source of truth for the unsaved change lives inside each editor
  -- The only reason we store a copy of the state here is because of the render function
  -- in the Mainframe view, which uses this derived state to show an unsaved indicator.
  -- Inside the Mainframe view we can inspect the state of the submodules (Haskell/JS/Marlowe)
  -- as their state is part of the MainFrame state, but we cannot inspect the state of the
  -- child components Blockly and ActusBlockly as we need a Query.
  , hasUnsavedChanges :: Boolean
  -- The initial language selected when you create/load a project indicates the workflow a user might take
  -- A user can start with a haskell/javascript example that eventually gets compiled into
  -- marlowe/blockly and run in the simulator, or can create a marlowe/blockly contract directly,
  -- which can be used interchangeably. This is used all across the site to know what are the posible
  -- transitions.
  , workflow :: Maybe Lang
  }

derive instance newtypeState :: Newtype State _

_view :: Lens' State View
_view = _Newtype <<< prop (SProxy :: SProxy "view")

_jsCompilationResult :: Lens' State CompilationState
_jsCompilationResult = _Newtype <<< prop (SProxy :: SProxy "jsCompilationResult")

_jsEditorKeybindings :: Lens' State KeyBindings
_jsEditorKeybindings = _Newtype <<< prop (SProxy :: SProxy "jsEditorKeybindings")

_activeJSDemo :: Lens' State String
_activeJSDemo = _Newtype <<< prop (SProxy :: SProxy "activeJSDemo")

_showBottomPanel :: Lens' State Boolean
_showBottomPanel = _Newtype <<< prop (SProxy :: SProxy "showBottomPanel")

_marloweEditorState :: Lens' State ME.State
_marloweEditorState = _Newtype <<< prop (SProxy :: SProxy "marloweEditorState")

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

_hasUnsavedChanges :: Lens' State Boolean
_hasUnsavedChanges = _Newtype <<< prop (SProxy :: SProxy "hasUnsavedChanges")

_workflow :: Lens' State (Maybe Lang)
_workflow = _Newtype <<< prop (SProxy :: SProxy "workflow")

currentLang :: State -> Maybe Lang
currentLang state = case state ^. _view of
  HaskellEditor -> Just Haskell
  JSEditor -> Just Javascript
  Simulation -> Just Marlowe
  BlocklyEditor -> Just Blockly
  ActusBlocklyEditor -> Just Actus
  _ -> Nothing

-- This function checks wether some action that we triggered requires the global state to be present.
-- Initially the code to track this was thought to handle a global boolean state that can be set from the
-- different handleActions, but I wasn't able to set it to false once the Projects modal has completed
-- loading the gists. The reason I wasn't able to do that is that we can't fire a MainFrame.handleAction
-- from a submodule action.
-- The good thing is that this becomes a derived state and we got a global loading for "Save" automatically.
-- The downside is that the logic is a little bit contrived. We may need to rethink when and why we use "_createGistResult"
hasGlobalLoading :: State -> Boolean
hasGlobalLoading state = Projects.modalIsLoading (state ^. _projects) || (projectIsLoadingOrSaving && not isSaveAsModal)
  where
  projectIsLoadingOrSaving = has (_createGistResult <<< _Loading) state

  -- If Action -> ModalView had an Eq instance, we could replace isSaveAsModal with
  -- has (_showModal <<< _Just <<< only SaveProjectAs) state
  isSaveAsModal = case state ^. _showModal of
    Just SaveProjectAs -> true
    _ -> false

-- editable
_timestamp ::
  forall s a.
  Lens' { timestamp :: a | s } a
_timestamp = prop (SProxy :: SProxy "timestamp")

_value :: forall s a. Lens' { value :: a | s } a
_value = prop (SProxy :: SProxy "value")

isActiveTab :: State -> View -> Array ClassName
isActiveTab state activeView = state ^. _view <<< (activeClass (eq activeView))
