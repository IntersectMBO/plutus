-- A separate module for types that are shared between Simulation and Simulation.BottomPanel
module Simulation.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Array (mapMaybe)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Getter', Lens', Prism', Traversal', lens, preview, prism, set, to, view)
import Data.Lens.At (at)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\))
import Foreign.Generic (class Decode, class Encode, genericDecode, genericEncode)
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Help (HelpContext(..))
import Marlowe.Holes (Holes)
import Marlowe.Semantics (AccountId, Assets, Bound, Case, ChoiceId, ChosenNum, Contract, Input, Observation, Party(..), Payee, Payment, Slot, SlotInterval, Timeout, Token, TransactionError, TransactionInput, TransactionWarning, Value, ValueId, aesonCompatibleOptions, emptyState)
import Marlowe.Semantics as S
import Marlowe.Symbolic.Types.Response (Result)
import Monaco (IMarker)
import Network.RemoteData (RemoteData)
import Projects.Types (Lang(..))
import Servant.PureScript.Ajax (AjaxError)
import Text.Parsing.StringParser (Pos)
import Web.HTML.Event.DragEvent (DragEvent)

data ActionInputId
  = DepositInputId AccountId Party Token BigInteger
  | ChoiceInputId ChoiceId
  | NotifyInputId
  | MoveToSlotId

derive instance eqActionInputId :: Eq ActionInputId

derive instance ordActionInputId :: Ord ActionInputId

derive instance genericActionInputId :: Generic ActionInputId _

instance encodeActionInputId :: Encode ActionInputId where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeActionInputId :: Decode ActionInputId where
  decode = genericDecode aesonCompatibleOptions

-- | On the front end we need Actions however we also need to keep track of the current
-- | choice that has been set for Choices
data ActionInput
  = DepositInput AccountId Party Token BigInteger
  | ChoiceInput ChoiceId (Array Bound) ChosenNum
  | NotifyInput
  | MoveToSlot Slot

derive instance eqActionInput :: Eq ActionInput

derive instance ordActionInput :: Ord ActionInput

derive instance genericActionInput :: Generic ActionInput _

instance encodeActionInput :: Encode ActionInput where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeActionInput :: Decode ActionInput where
  decode = genericDecode aesonCompatibleOptions

newtype Parties
  = Parties (Map Party (Map ActionInputId ActionInput))

derive instance newtypeParties :: Newtype Parties _

derive newtype instance semigroupParties :: Semigroup Parties

derive newtype instance monoidParties :: Monoid Parties

mapPartiesActionInput :: (ActionInput -> ActionInput) -> Parties -> Parties
mapPartiesActionInput f (Parties m) = Parties $ (map <<< map) f m

derive newtype instance encodeParties :: Encode Parties

derive newtype instance decodeParties :: Decode Parties

_actionInput :: Party -> ActionInputId -> Traversal' Parties ActionInput
_actionInput party id = _Newtype <<< ix party <<< ix id

_otherActions :: Traversal' Parties (Map ActionInputId ActionInput)
_otherActions = _Newtype <<< ix otherActionsParty

_moveToAction :: Lens' Parties (Maybe ActionInput)
_moveToAction = lens get' set'
  where
  get' = preview (_actionInput otherActionsParty MoveToSlotId)

  set' p ma =
    let
      m = case preview _otherActions p, ma of
        Nothing, Nothing -> Nothing
        Just m', Nothing -> Just $ Map.delete MoveToSlotId m'
        Nothing, Just a -> Just $ Map.singleton MoveToSlotId a
        Just m', Just a -> Just $ Map.insert MoveToSlotId a m'
    in
      set (_Newtype <<< at otherActionsParty) m p

data MarloweEvent
  = InputEvent TransactionInput
  | OutputEvent SlotInterval Payment

derive instance genericMarloweEvent :: Generic MarloweEvent _

instance encodeMarloweEvent :: Encode MarloweEvent where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeMarloweEvent :: Decode MarloweEvent where
  decode = genericDecode aesonCompatibleOptions

-- We have a special person for notifications
otherActionsParty :: Party
otherActionsParty = Role "marlowe_other_actions"

type ExecutionStateRecord
  = { possibleActions :: Parties
    , pendingInputs :: Array Input
    , transactionError :: Maybe TransactionError
    , transactionWarnings :: Array TransactionWarning
    , log :: Array MarloweEvent
    , state :: S.State
    , slot :: Slot
    , moneyInContract :: Assets
    }

_possibleActions :: forall s a. Lens' { possibleActions :: a | s } a
_possibleActions = prop (SProxy :: SProxy "possibleActions")

_pendingInputs :: forall s a. Lens' { pendingInputs :: a | s } a
_pendingInputs = prop (SProxy :: SProxy "pendingInputs")

_state :: forall s a. Lens' { state :: a | s } a
_state = prop (SProxy :: SProxy "state")

_transactionError :: forall s a. Lens' { transactionError :: a | s } a
_transactionError = prop (SProxy :: SProxy "transactionError")

_transactionWarnings :: forall s a. Lens' { transactionWarnings :: a | s } a
_transactionWarnings = prop (SProxy :: SProxy "transactionWarnings")

_slot :: forall s a. Lens' { slot :: a | s } a
_slot = prop (SProxy :: SProxy "slot")

_moneyInContract :: forall s a. Lens' { moneyInContract :: a | s } a
_moneyInContract = prop (SProxy :: SProxy "moneyInContract")

_log :: forall s a. Lens' { log :: a | s } a
_log = prop (SProxy :: SProxy "log")

_payments :: forall s. Getter' { log :: Array MarloweEvent | s } (Array Payment)
_payments = _log <<< to (mapMaybe f)
  where
  f (InputEvent _) = Nothing

  f (OutputEvent _ payment) = Just payment

type InitialConditionsRecord
  = { initialSlot :: Slot }

_initialSlot :: forall s a. Lens' { initialSlot :: a | s } a
_initialSlot = prop (SProxy :: SProxy "initialSlot")

data ExecutionState
  = SimulationRunning ExecutionStateRecord
  | SimulationNotStarted InitialConditionsRecord

-- | Prism for the `ExecutionState` constructor of `SimulationRunning`.
_SimulationRunning :: Prism' ExecutionState ExecutionStateRecord
_SimulationRunning =
  prism SimulationRunning
    $ ( \x -> case x of
          SimulationRunning record -> Right record
          anotherCase -> Left anotherCase
      )

-- | Prism for the `ExecutionState` constructor of `SimulationNotStarted`.
_SimulationNotStarted :: Prism' ExecutionState InitialConditionsRecord
_SimulationNotStarted =
  prism SimulationNotStarted
    $ ( \x -> case x of
          SimulationNotStarted record -> Right record
          anotherCase -> Left anotherCase
      )

emptyExecutionStateWithSlot :: Slot -> ExecutionState
emptyExecutionStateWithSlot sn =
  SimulationRunning
    { possibleActions: mempty
    , pendingInputs: mempty
    , transactionError: Nothing
    , transactionWarnings: mempty
    , log: mempty
    , state: emptyState sn
    , slot: sn
    , moneyInContract: mempty
    }

simulationNotStartedWithSlot :: Slot -> ExecutionState
simulationNotStartedWithSlot slot = SimulationNotStarted { initialSlot: slot }

simulationNotStarted :: ExecutionState
simulationNotStarted = simulationNotStartedWithSlot zero

type MarloweState
  = { executionState :: ExecutionState
    , contract :: Maybe Contract
    , editorErrors :: Array IMarker
    , editorWarnings :: Array IMarker
    , holes :: Holes
    }

_executionState :: forall s a. Lens' { executionState :: a | s } a
_executionState = prop (SProxy :: SProxy "executionState")

_contract :: forall s a. Lens' { contract :: a | s } a
_contract = prop (SProxy :: SProxy "contract")

_editorErrors :: forall s a. Lens' { editorErrors :: a | s } a
_editorErrors = prop (SProxy :: SProxy "editorErrors")

_editorWarnings :: forall s a. Lens' { editorWarnings :: a | s } a
_editorWarnings = prop (SProxy :: SProxy "editorWarnings")

_holes :: forall s a. Lens' { holes :: a | s } a
_holes = prop (SProxy :: SProxy "holes")

--- Language.Haskell.Interpreter ---
_result :: forall s a. Lens' { result :: a | s } a
_result = prop (SProxy :: SProxy "result")

emptyMarloweState :: MarloweState
emptyMarloweState =
  { contract: Nothing
  , editorErrors: mempty
  , editorWarnings: mempty
  , holes: mempty
  , executionState: simulationNotStarted
  }

emptyMarloweStateWithSlot :: Slot -> MarloweState
emptyMarloweStateWithSlot sn =
  { contract: Nothing
  , editorErrors: mempty
  , editorWarnings: mempty
  , holes: mempty
  , executionState: emptyExecutionStateWithSlot sn
  }

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

derive instance ordContractPathStep :: Ord ContractPathStep

derive instance genericContractPathStep :: Generic ContractPathStep _

instance showContractPathStep :: Show ContractPathStep where
  show = genericShow

type ContractPath
  = List ContractPathStep

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

type State
  = { showRightPanel :: Boolean
    , marloweState :: NonEmptyList MarloweState
    , helpContext :: HelpContext
    -- FIXME: remove editorKeybindings
    , editorKeybindings :: KeyBindings
    , showBottomPanel :: Boolean
    , showErrorDetail :: Boolean
    , bottomPanelView :: BottomPanelView
    , analysisState :: AnalysisState
    -- FIXME: Remove selectedHole
    , selectedHole :: Maybe String
    , oldContract :: Maybe String
    , source :: Lang
    , hasUnsavedChanges :: Boolean
    }

_showRightPanel :: Lens' State Boolean
_showRightPanel = prop (SProxy :: SProxy "showRightPanel")

_marloweState :: forall s. Lens' { marloweState :: NonEmptyList MarloweState | s } (NonEmptyList MarloweState)
_marloweState = prop (SProxy :: SProxy "marloweState")

_currentMarloweState :: forall s. Lens' { marloweState :: NonEmptyList MarloweState | s } MarloweState
_currentMarloweState = _marloweState <<< _Head

_currentContract :: Lens' State (Maybe Contract)
_currentContract = _currentMarloweState <<< _contract

_helpContext :: Lens' State HelpContext
_helpContext = prop (SProxy :: SProxy "helpContext")

_editorKeybindings :: Lens' State KeyBindings
_editorKeybindings = prop (SProxy :: SProxy "editorKeybindings")

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

_source :: Lens' State Lang
_source = prop (SProxy :: SProxy "source")

mkState :: State
mkState =
  { showRightPanel: true
  , marloweState: NEL.singleton emptyMarloweState
  , helpContext: MarloweHelp
  , editorKeybindings: DefaultBindings
  , showBottomPanel: true
  , showErrorDetail: false
  , bottomPanelView: CurrentStateView
  , analysisState: NoneAsked
  , selectedHole: Nothing
  , oldContract: Nothing
  , source: Marlowe
  , hasUnsavedChanges: false
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
  | InitMarloweProject String
  | MarkProjectAsSaved
  -- marlowe actions
  | SetInitialSlot Slot
  | StartSimulation
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
  -- Editors
  | SetBlocklyCode
  | EditHaskell
  | EditJavascript
  | EditActus
  -- websocket
  | AnalyseContract
  | AnalyseReachabilityContract
  | Save

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "Simulation." <> s

instance isEventAction :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (HandleEditorMessage _) = Just $ defaultEvent "HandleEditorMessage"
  toEvent (HandleDragEvent _) = Just $ defaultEvent "HandleDragEvent"
  toEvent (HandleDropEvent _) = Just $ defaultEvent "HandleDropEvent"
  toEvent (MoveToPosition _ _) = Just $ defaultEvent "MoveToPosition"
  toEvent (SelectEditorKeyBindings _) = Just $ defaultEvent "SelectEditorKeyBindings"
  toEvent (LoadScript script) = Just $ (defaultEvent "LoadScript") { label = Just script }
  toEvent (SetEditorText _) = Just $ defaultEvent "SetEditorText"
  toEvent (SetInitialSlot _) = Just $ defaultEvent "SetInitialSlot"
  toEvent StartSimulation = Just $ defaultEvent "StartSimulation"
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
  toEvent (ShowRightPanel _) = Just $ defaultEvent "ShowRightPanel"
  toEvent (ShowBottomPanel _) = Just $ defaultEvent "ShowBottomPanel"
  toEvent (ShowErrorDetail _) = Just $ defaultEvent "ShowErrorDetail"
  toEvent SetBlocklyCode = Just $ defaultEvent "SetBlocklyCode"
  toEvent EditHaskell = Just $ defaultEvent "EditHaskell"
  toEvent EditJavascript = Just $ defaultEvent "EditJavascript"
  toEvent EditActus = Just $ defaultEvent "EditActus"
  toEvent AnalyseContract = Just $ defaultEvent "AnalyseContract"
  toEvent AnalyseReachabilityContract = Just $ defaultEvent "AnalyseReachabilityContract"
  toEvent Save = Just $ defaultEvent "Save"
  toEvent (InitMarloweProject _) = Just $ defaultEvent "InitMarloweProject"
  toEvent MarkProjectAsSaved = Just $ defaultEvent "MarkProjectAsSaved"

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
