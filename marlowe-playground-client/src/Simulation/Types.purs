-- A separate module for types that are shared between Simulation and Simulation.BottomPanel
module Simulation.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Auth (AuthStatus)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens', to, view)
import Data.Lens.NonEmptyList (_Head)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Maybe (Maybe(..), isJust)
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\))
import Gist (Gist)
import Gists (GistAction)
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Help (HelpContext(..))
import Marlowe.Semantics (Bound, ChoiceId, ChosenNum, Contract, Input, Slot)
import Marlowe.Semantics as S
import Marlowe.Symbolic.Types.Response (Result)
import Network.RemoteData (RemoteData(..))
import Servant.PureScript.Ajax (AjaxError)
import Simulation.State (MarloweState, _contract, _editorErrors, emptyMarloweState)
import Text.Parsing.StringParser (Pos)
import Web.HTML.Event.DragEvent (DragEvent)

type WebData
  = RemoteData AjaxError

data ContractPathStep
  = PayContPath
  | IfTruePath
  | IfFalsePath
  | WhenCasePath Int
  | WhenTimeoutPath
  | LetPath
  | AssertPath

derive instance eqContractPathStep :: Eq ContractPathStep

derive instance genericContractPathStep :: Generic ContractPathStep _

instance showContractPathStep :: Show ContractPathStep where
  show = genericShow

type ContractPath
  = List ContractPathStep

data ReachabilityAnalysisData
  = NotStarted
  | InProgress
    { currPath :: ContractPath
    , currContract :: Contract
    , originalState :: S.State
    , subproblems :: List (Unit -> ContractPath /\ Contract)
    , numSubproblems :: Int
    , numSolvedSubproblems :: Int
    }
  | ReachabilityFailure String
  | UnreachableSubcontract ContractPath
  | AllReachable

data AnalysisState
  = NoneAsked
  | WarningAnalysis (WebData Result)
  | ReachabilityAnalysis ReachabilityAnalysisData

type State
  = { showRightPanel :: Boolean
    , marloweState :: NonEmptyList MarloweState
    , activeDemo :: String
    , helpContext :: HelpContext
    , editorKeybindings :: KeyBindings
    , authStatus :: WebData AuthStatus
    -- TODO: gist state is duplicated until SCP-1256, these 3 fields should be removed as part of that
    , gistUrl :: Maybe String
    , createGistResult :: WebData Gist
    , loadGistResult :: Either String (WebData Gist)
    , showBottomPanel :: Boolean
    , showErrorDetail :: Boolean
    , bottomPanelView :: BottomPanelView
    , analysisState :: AnalysisState
    , selectedHole :: Maybe String
    , oldContract :: Maybe String
    }

_showRightPanel :: Lens' State Boolean
_showRightPanel = prop (SProxy :: SProxy "showRightPanel")

_currentMarloweState :: Lens' State MarloweState
_currentMarloweState = _marloweState <<< _Head

_marloweState :: Lens' State (NonEmptyList MarloweState)
_marloweState = prop (SProxy :: SProxy "marloweState")

_currentContract :: Lens' State (Maybe Contract)
_currentContract = _currentMarloweState <<< _contract

_activeDemo :: Lens' State String
_activeDemo = prop (SProxy :: SProxy "activeDemo")

_helpContext :: Lens' State HelpContext
_helpContext = prop (SProxy :: SProxy "helpContext")

_editorKeybindings :: Lens' State KeyBindings
_editorKeybindings = prop (SProxy :: SProxy "editorKeybindings")

_authStatus :: Lens' State (WebData AuthStatus)
_authStatus = prop (SProxy :: SProxy "authStatus")

_gistUrl :: Lens' State (Maybe String)
_gistUrl = prop (SProxy :: SProxy "gistUrl")

_createGistResult :: Lens' State (WebData Gist)
_createGistResult = prop (SProxy :: SProxy "createGistResult")

_loadGistResult :: Lens' State (Either String (WebData Gist))
_loadGistResult = prop (SProxy :: SProxy "loadGistResult")

_showBottomPanel :: Lens' State Boolean
_showBottomPanel = prop (SProxy :: SProxy "showBottomPanel")

_showErrorDetail :: Lens' State Boolean
_showErrorDetail = prop (SProxy :: SProxy "showErrorDetail")

_bottomPanelView :: Lens' State BottomPanelView
_bottomPanelView = prop (SProxy :: SProxy "bottomPanelView")

_analysisState :: Lens' State AnalysisState
_analysisState = prop (SProxy :: SProxy "analysisState")

_selectedHole :: Lens' State (Maybe String)
_selectedHole = prop (SProxy :: SProxy "selectedHole")

_oldContract :: Lens' State (Maybe String)
_oldContract = prop (SProxy :: SProxy "oldContract")

mkState :: State
mkState =
  { showRightPanel: true
  , marloweState: NEL.singleton (emptyMarloweState zero)
  , activeDemo: mempty
  , helpContext: MarloweHelp
  , editorKeybindings: DefaultBindings
  , authStatus: NotAsked
  , gistUrl: Nothing
  , createGistResult: NotAsked
  , loadGistResult: Right NotAsked
  , showBottomPanel: true
  , showErrorDetail: false
  , bottomPanelView: CurrentStateView
  , analysisState: NoneAsked
  , selectedHole: Nothing
  , oldContract: Nothing
  }

isContractValid :: State -> Boolean
isContractValid state =
  (view (_marloweState <<< _Head <<< _contract <<< to isJust) state)
    && (view (_marloweState <<< _Head <<< _editorErrors <<< to Array.null) state)

data Action
  = Init
  -- editor
  | HandleEditorMessage Monaco.Message
  | HandleDragEvent DragEvent
  | HandleDropEvent DragEvent
  | MoveToPosition Pos Pos
  | SelectEditorKeyBindings KeyBindings
  | LoadScript String
  | SetEditorText String
  -- Gist support.
  | CheckAuthStatus
  | GistAction GistAction
  -- marlowe actions
  | MoveSlot Slot
  | SetSlot Slot
  | AddInput Input (Array Bound)
  | RemoveInput Input
  | SetChoice ChoiceId ChosenNum
  | ResetContract
  | ResetSimulator
  | Undo
  | SelectHole (Maybe String)
  -- simulation view
  | ChangeSimulationView BottomPanelView
  | ChangeHelpContext HelpContext
  | ShowRightPanel Boolean
  | ShowBottomPanel Boolean
  | ShowErrorDetail Boolean
  -- Blockly
  | SetBlocklyCode
  -- websocket
  | AnalyseContract
  | AnalyseReachabilityContract

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "Simulation." <> s

instance isEventAction :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (HandleEditorMessage _) = Just $ defaultEvent "HandleEditorMessage"
  toEvent (HandleDragEvent _) = Just $ defaultEvent "HandleDragEvent"
  toEvent (HandleDropEvent _) = Just $ defaultEvent "HandleDropEvent"
  toEvent (MoveToPosition _ _) = Just $ defaultEvent "MoveToPosition"
  toEvent (SelectEditorKeyBindings _) = Just $ defaultEvent "SelectEditorKeyBindings"
  toEvent CheckAuthStatus = Just $ defaultEvent "CheckAuthStatus"
  toEvent (LoadScript script) = Just $ (defaultEvent "LoadScript") { label = Just script }
  toEvent (SetEditorText _) = Just $ defaultEvent "SetEditorText"
  toEvent (MoveSlot _) = Just $ defaultEvent "MoveSlot"
  toEvent (SetSlot _) = Just $ defaultEvent "SetSlot"
  toEvent (AddInput _ _) = Just $ defaultEvent "AddInput"
  toEvent (RemoveInput _) = Just $ defaultEvent "RemoveInput"
  toEvent (SetChoice _ _) = Just $ defaultEvent "SetChoice"
  toEvent ResetSimulator = Just $ defaultEvent "ResetSimulator"
  toEvent ResetContract = Just $ defaultEvent "ResetContract"
  toEvent Undo = Just $ defaultEvent "Undo"
  toEvent (SelectHole _) = Just $ defaultEvent "SelectHole"
  toEvent (ChangeSimulationView view) = Just $ (defaultEvent "ChangeSimulationView") { label = Just $ show view }
  toEvent (ChangeHelpContext help) = Just $ (defaultEvent "ChangeHelpContext") { label = Just $ show help }
  toEvent (GistAction _) = Just $ defaultEvent "GistAction"
  toEvent (ShowRightPanel _) = Just $ defaultEvent "ShowRightPanel"
  toEvent (ShowBottomPanel _) = Just $ defaultEvent "ShowBottomPanel"
  toEvent (ShowErrorDetail _) = Just $ defaultEvent "ShowErrorDetail"
  toEvent SetBlocklyCode = Just $ defaultEvent "SetBlocklyCode"
  toEvent AnalyseContract = Just $ defaultEvent "AnalyseContract"
  toEvent AnalyseReachabilityContract = Just $ defaultEvent "AnalyseReachabilityContract"

data Query a
  = WebsocketResponse (RemoteData String Result) a

data BottomPanelView
  = CurrentStateView
  | StaticAnalysisView
  | MarloweErrorsView
  | MarloweWarningsView
  | MarloweLogView

derive instance eqBottomPanelView :: Eq BottomPanelView

derive instance genericBottomPanelView :: Generic BottomPanelView _

instance showBottomPanelView :: Show BottomPanelView where
  show = genericShow
