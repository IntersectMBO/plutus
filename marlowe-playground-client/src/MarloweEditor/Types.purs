module MarloweEditor.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import BottomPanel.Types as BottomPanel
import Data.Array (filter)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens', to, view, (^.))
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains)
import Data.Symbol (SProxy(..))
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Marlowe.Extended (IntegerTemplateType)
import Monaco (IMarker)
import StaticAnalysis.Types (AnalysisExecutionState(..), AnalysisState)
import Text.Parsing.StringParser (Pos)
import Web.HTML.Event.DragEvent (DragEvent)

data Action
  = Init
  | ChangeKeyBindings KeyBindings
  | HandleEditorMessage Monaco.Message
  | HandleDragEvent DragEvent
  | HandleDropEvent DragEvent
  | MoveToPosition Pos Pos
  | LoadScript String
  | SetEditorText String
  | BottomPanelAction (BottomPanel.Action BottomPanelView Action)
  | ShowErrorDetail Boolean
  | SendToSimulator
  | ViewAsBlockly
  | InitMarloweProject String
  | SelectHole (Maybe String)
  | SetIntegerTemplateParam IntegerTemplateType String BigInteger
  | AnalyseContract
  | AnalyseReachabilityContract
  | AnalyseContractForCloseRefund
  | ClearAnalysisResults
  | Save

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "MarloweEditor." <> s

instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (ChangeKeyBindings _) = Just $ defaultEvent "ChangeKeyBindings"
  toEvent (HandleEditorMessage _) = Just $ defaultEvent "HandleEditorMessage"
  toEvent (HandleDragEvent _) = Just $ defaultEvent "HandleDragEvent"
  toEvent (HandleDropEvent _) = Just $ defaultEvent "HandleDropEvent"
  toEvent (MoveToPosition _ _) = Just $ defaultEvent "MoveToPosition"
  toEvent (LoadScript script) = Just $ (defaultEvent "LoadScript") { label = Just script }
  toEvent (SetEditorText _) = Just $ defaultEvent "SetEditorText"
  toEvent (BottomPanelAction action) = A.toEvent action
  toEvent (ShowErrorDetail _) = Just $ defaultEvent "ShowErrorDetail"
  toEvent SendToSimulator = Just $ defaultEvent "SendToSimulator"
  toEvent ViewAsBlockly = Just $ defaultEvent "ViewAsBlockly"
  toEvent (InitMarloweProject _) = Just $ defaultEvent "InitMarloweProject"
  toEvent (SelectHole _) = Just $ defaultEvent "SelectHole"
  toEvent (SetIntegerTemplateParam _ _ _) = Just $ defaultEvent "SetIntegerTemplateParam"
  toEvent AnalyseContract = Just $ defaultEvent "AnalyseContract"
  toEvent AnalyseReachabilityContract = Just $ defaultEvent "AnalyseReachabilityContract"
  toEvent AnalyseContractForCloseRefund = Just $ defaultEvent "AnalyseContractForCloseRefund"
  toEvent ClearAnalysisResults = Just $ defaultEvent "ClearAnalysisResults"
  toEvent Save = Just $ defaultEvent "Save"

data BottomPanelView
  = StaticAnalysisView
  | MarloweErrorsView
  | MarloweWarningsView

derive instance eqBottomPanelView :: Eq BottomPanelView

derive instance genericBottomPanelView :: Generic BottomPanelView _

instance showBottomPanelView :: Show BottomPanelView where
  show = genericShow

type State
  = { keybindings :: KeyBindings
    , bottomPanelState :: BottomPanel.State BottomPanelView
    , showErrorDetail :: Boolean
    , selectedHole :: Maybe String
    , analysisState :: AnalysisState
    , editorErrors :: Array IMarker
    , editorWarnings :: Array IMarker
    }

_keybindings :: Lens' State KeyBindings
_keybindings = prop (SProxy :: SProxy "keybindings")

_showErrorDetail :: Lens' State Boolean
_showErrorDetail = prop (SProxy :: SProxy "showErrorDetail")

_selectedHole :: Lens' State (Maybe String)
_selectedHole = prop (SProxy :: SProxy "selectedHole")

_editorErrors :: forall s a. Lens' { editorErrors :: a | s } a
_editorErrors = prop (SProxy :: SProxy "editorErrors")

_editorWarnings :: forall s a. Lens' { editorWarnings :: a | s } a
_editorWarnings = prop (SProxy :: SProxy "editorWarnings")

_bottomPanelState :: Lens' State (BottomPanel.State BottomPanelView)
_bottomPanelState = prop (SProxy :: SProxy "bottomPanelState")

initialState :: State
initialState =
  { keybindings: DefaultBindings
  , bottomPanelState: BottomPanel.initialState StaticAnalysisView
  , showErrorDetail: false
  , selectedHole: Nothing
  , analysisState:
      { templateContent: mempty
      , analysisExecutionState: NoneAsked
      }
  , editorErrors: mempty
  , editorWarnings: mempty
  }

contractHasHoles :: State -> Boolean
contractHasHoles state =
  let
    warnings = state ^. _editorWarnings

    holes = filter (\warning -> contains (Pattern "hole") warning.message) warnings
  in
    not $ Array.null holes

contractHasErrors :: State -> Boolean
contractHasErrors state = not $ view (_editorErrors <<< to Array.null) state
