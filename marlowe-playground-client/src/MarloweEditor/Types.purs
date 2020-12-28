module MarloweEditor.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Array (filter)
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens', to, view, (^.))
import Data.Lens.Record (prop)
import Data.List (List)
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.String (Pattern(..), contains)
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\))
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Marlowe.Semantics (AccountId, Case, Contract, Observation, Payee, Timeout, Token, Value, ValueId)
import Marlowe.Semantics as S
import Marlowe.Symbolic.Types.Response (Result)
import Monaco (IMarker)
import Text.Parsing.StringParser (Pos)
import Types (WebData)
import Web.HTML.Event.DragEvent (DragEvent)

data Action
  = ChangeKeyBindings KeyBindings
  | HandleEditorMessage Monaco.Message
  | HandleDragEvent DragEvent
  | HandleDropEvent DragEvent
  | MoveToPosition Pos Pos
  | LoadScript String
  | SetEditorText String
  | ShowBottomPanel Boolean
  | ShowErrorDetail Boolean
  | ChangeBottomPanelView BottomPanelView
  | SendToSimulator
  | ViewAsBlockly
  | InitMarloweProject String
  | MarkProjectAsSaved
  -- websocket
  | AnalyseContract
  | AnalyseReachabilityContract
  | Save

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "MarloweEditor." <> s

instance actionIsEvent :: IsEvent Action where
  toEvent (ChangeKeyBindings _) = Just $ defaultEvent "ChangeKeyBindings"
  toEvent (HandleEditorMessage _) = Just $ defaultEvent "HandleEditorMessage"
  toEvent (HandleDragEvent _) = Just $ defaultEvent "HandleDragEvent"
  toEvent (HandleDropEvent _) = Just $ defaultEvent "HandleDropEvent"
  toEvent (MoveToPosition _ _) = Just $ defaultEvent "MoveToPosition"
  toEvent (LoadScript script) = Just $ (defaultEvent "LoadScript") { label = Just script }
  toEvent (SetEditorText _) = Just $ defaultEvent "SetEditorText"
  toEvent (ShowBottomPanel _) = Just $ defaultEvent "ShowBottomPanel"
  toEvent (ShowErrorDetail _) = Just $ defaultEvent "ShowErrorDetail"
  toEvent (ChangeBottomPanelView view) = Just $ (defaultEvent "ChangeBottomPanelView") { label = Just $ show view }
  toEvent SendToSimulator = Just $ defaultEvent "SendToSimulator"
  toEvent ViewAsBlockly = Just $ defaultEvent "ViewAsBlockly"
  toEvent (InitMarloweProject _) = Just $ defaultEvent "InitMarloweProject"
  toEvent MarkProjectAsSaved = Just $ defaultEvent "MarkProjectAsSaved"
  toEvent AnalyseContract = Just $ defaultEvent "AnalyseContract"
  toEvent AnalyseReachabilityContract = Just $ defaultEvent "AnalyseReachabilityContract"
  toEvent Save = Just $ defaultEvent "Save"

data ContractZipper
  = PayZip AccountId Payee Token Value ContractZipper
  | IfTrueZip Observation ContractZipper Contract
  | IfFalseZip Observation Contract ContractZipper
  | WhenCaseZip (List Case) S.Action ContractZipper (List Case) Timeout Contract -- First list is stored reversed for efficiency
  | WhenTimeoutZip (Array Case) Timeout ContractZipper
  | LetZip ValueId Value ContractZipper
  | AssertZip Observation ContractZipper
  | HeadZip

type PrefixMap
  = Map ContractPathStep (Set (NonEmptyList ContractPathStep))

data ContractPathStep
  = PayContPath
  | IfTruePath
  | IfFalsePath
  | WhenCasePath Int
  | WhenTimeoutPath
  | LetPath
  | AssertPath

derive instance eqContractPathStep :: Eq ContractPathStep

derive instance ordContractPathStep :: Ord ContractPathStep

derive instance genericContractPathStep :: Generic ContractPathStep _

instance showContractPathStep :: Show ContractPathStep where
  show = genericShow

type ContractPath
  = List ContractPathStep

type RemainingSubProblemInfo
  = List (ContractZipper /\ Contract)

type AnalysisInProgressRecord
  = { currPath :: ContractPath
    , currContract :: Contract
    , currChildren :: RemainingSubProblemInfo
    , originalState :: S.State
    , originalContract :: Contract
    , subproblems :: RemainingSubProblemInfo
    , numSubproblems :: Int
    , numSolvedSubproblems :: Int
    , counterExampleSubcontracts :: List ContractPath
    }

type AnalysisCounterExamplesRecord
  = { originalState :: S.State
    , originalContract :: Contract
    , counterExampleSubcontracts :: NonEmptyList ContractPath
    }

data MultiStageAnalysisData
  = AnalysisNotStarted
  | AnalysisInProgress AnalysisInProgressRecord
  | AnalyisisFailure String
  | AnalysisFoundCounterExamples AnalysisCounterExamplesRecord
  | AnalysisFinishedAndPassed

data AnalysisState
  = NoneAsked
  | WarningAnalysis (WebData Result)
  | ReachabilityAnalysis MultiStageAnalysisData

type MultiStageAnalysisProblemDef
  = { expandSubproblemImpl :: ContractZipper -> Contract -> (ContractPath /\ Contract)
    , isValidSubproblemImpl :: ContractZipper -> Contract -> Boolean
    , analysisDataSetter :: MultiStageAnalysisData -> AnalysisState
    }

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
    , showBottomPanel :: Boolean
    , showErrorDetail :: Boolean
    , bottomPanelView :: BottomPanelView
    , hasUnsavedChanges :: Boolean
    , selectedHole :: Maybe String
    -- This is pagination information that we need to provide to the haskell backend
    -- so that it can do the analysis in chunks
    , analysisState :: AnalysisState
    , editorErrors :: Array IMarker
    , editorWarnings :: Array IMarker
    }

_keybindings :: Lens' State KeyBindings
_keybindings = prop (SProxy :: SProxy "keybindings")

_showBottomPanel :: Lens' State Boolean
_showBottomPanel = prop (SProxy :: SProxy "showBottomPanel")

_showErrorDetail :: Lens' State Boolean
_showErrorDetail = prop (SProxy :: SProxy "showErrorDetail")

_selectedHole :: Lens' State (Maybe String)
_selectedHole = prop (SProxy :: SProxy "selectedHole")

_analysisState :: Lens' State AnalysisState
_analysisState = prop (SProxy :: SProxy "analysisState")

_editorErrors :: forall s a. Lens' { editorErrors :: a | s } a
_editorErrors = prop (SProxy :: SProxy "editorErrors")

_editorWarnings :: forall s a. Lens' { editorWarnings :: a | s } a
_editorWarnings = prop (SProxy :: SProxy "editorWarnings")

_bottomPanelView :: Lens' State BottomPanelView
_bottomPanelView = prop (SProxy :: SProxy "bottomPanelView")

initialState :: State
initialState =
  { keybindings: DefaultBindings
  , showBottomPanel: false
  , showErrorDetail: false
  , bottomPanelView: StaticAnalysisView
  , hasUnsavedChanges: false
  , selectedHole: Nothing
  , analysisState: NoneAsked
  , editorErrors: mempty
  , editorWarnings: mempty
  }

-- Check if we could convert to a valid contract. Meaning one that has no errors and may have
-- warnings, but no holes.
isValidContract :: State -> Boolean
isValidContract state =
  let
    errors = state ^. _editorErrors

    warnings = state ^. _editorWarnings

    holes = filter (\warning -> contains (Pattern "hole") warning.message) warnings
  in
    Array.null errors && Array.null holes

isValidContractWithHoles :: State -> Boolean
isValidContractWithHoles state = view (_editorErrors <<< to Array.null) state
