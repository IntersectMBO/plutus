module Types where

import API (RunResult)
import Ace.Halogen.Component (AceMessage, AceQuery)
import Auth (AuthStatus)
import Blockly.Types (BlocklyState)
import Data.Array (uncons)
import Data.BigInteger (BigInteger)
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Json.JsonEither (JsonEither)
import Data.Lens (Lens, Lens', lens, (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.NonEmpty (foldl1, (:|))
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Editor as Editor
import Gist (Gist)
import Gists (GistAction)
import Halogen as H
import Halogen.Blockly (BlocklyQuery, BlocklyMessage)
import Halogen.Monaco as Monaco
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult)
import Marlowe.Holes (Holes, MarloweHole)
import Marlowe.Semantics (AccountId, Action(..), Assets, Bound, ChoiceId, ChosenNum, Contract, Environment(..), Input, Party, Payment, PubKey, Slot, SlotInterval(..), State, Token, TransactionError, TransactionWarning, _minSlot, boundFrom, emptyState, evalValue)
import Marlowe.Symbolic.Types.Response (Result)
import Monaco (IMarker)
import Network.RemoteData (RemoteData)
import Prelude (class Eq, class Ord, class Show, Unit, map, mempty, min, zero, (<<<))
import Servant.PureScript.Ajax (AjaxError)
import Text.Parsing.StringParser (Pos)
import Type.Data.Boolean (kind Boolean)
import Web.HTML.Event.DragEvent (DragEvent)

_Head :: forall a. Lens (NonEmptyList a) (NonEmptyList a) a a
_Head = lens NEL.head (\l new -> let { head, tail } = NEL.uncons l in NEL.cons' new tail)

------------------------------------------------------------
data HQuery a
  = ReceiveWebsocketMessage String a

data HAction
  -- Haskell Editor
  = MarloweHandleEditorMessage Monaco.Message
  | MarloweHandleDragEvent DragEvent
  | MarloweHandleDropEvent DragEvent
  | MarloweMoveToPosition Pos Pos
  | HaskellEditorAction Editor.Action
  -- Gist support.
  | CheckAuthStatus
  | GistAction GistAction
  -- haskell actions
  | CompileHaskellProgram
  | ChangeView View
  | SendResult
  | LoadHaskellScript String
  | LoadMarloweScript String
  -- marlowe actions
  | ApplyTransaction
  | NextSlot
  | AddInput (Maybe PubKey) Input (Array Bound)
  | RemoveInput (Maybe PubKey) Input
  | SetChoice ChoiceId ChosenNum
  | ResetSimulator
  | Undo
  | SelectHole (Maybe String)
  | InsertHole String MarloweHole (Array MarloweHole)
  -- simulation view
  | ChangeSimulationView SimulationBottomPanelView
  | ChangeHelpContext HelpContext
  | ShowRightPanel Boolean
  | ShowBottomPanel Boolean
  | ShowErrorDetail Boolean
  -- blockly
  | HandleBlocklyMessage BlocklyMessage
  | SetBlocklyCode
  -- websocket
  | AnalyseContract

data Message
  = WebsocketMessage String

------------------------------------------------------------
type ChildSlots
  = ( haskellEditorSlot :: H.Slot AceQuery AceMessage Unit
    , marloweEditorSlot :: H.Slot Monaco.Query Monaco.Message Unit
    , blocklySlot :: H.Slot BlocklyQuery BlocklyMessage Unit
    )

_haskellEditorSlot :: SProxy "haskellEditorSlot"
_haskellEditorSlot = SProxy

_marloweEditorSlot :: SProxy "marloweEditorSlot"
_marloweEditorSlot = SProxy

_blocklySlot :: SProxy "blocklySlot"
_blocklySlot = SProxy

-----------------------------------------------------------
data View
  = HaskellEditor
  | Simulation
  | BlocklyEditor

derive instance eqView :: Eq View

derive instance genericView :: Generic View _

instance showView :: Show View where
  show = genericShow

data SimulationBottomPanelView
  = CurrentStateView
  | StaticAnalysisView
  | MarloweErrorsView
  | MarloweWarningsView

derive instance eqSimulationBottomPanelView :: Eq SimulationBottomPanelView

derive instance genericSimulationBottomPanelView :: Generic SimulationBottomPanelView _

instance showSimulationBottomPanelView :: Show SimulationBottomPanelView where
  show = genericShow

newtype FrontendState
  = FrontendState
  { view :: View
  , simulationBottomPanelView :: SimulationBottomPanelView
  , editorPreferences :: Editor.Preferences
  , compilationResult :: WebData (JsonEither InterpreterError (InterpreterResult RunResult))
  , marloweCompileResult :: Either (Array MarloweError) Unit
  , authStatus :: WebData AuthStatus
  , createGistResult :: WebData Gist
  , loadGistResult :: Either String (WebData Gist)
  , gistUrl :: Maybe String
  , marloweState :: NonEmptyList MarloweState
  , oldContract :: Maybe String
  , blocklyState :: Maybe BlocklyState
  , analysisState :: RemoteData String Result
  , selectedHole :: Maybe String
  , helpContext :: HelpContext
  , showRightPanel :: Boolean
  , showBottomPanel :: Boolean
  , showErrorDetail :: Boolean
  }

derive instance newtypeFrontendState :: Newtype FrontendState _

data MarloweError
  = MarloweError String

_view :: Lens' FrontendState View
_view = _Newtype <<< prop (SProxy :: SProxy "view")

_simulationBottomPanelView :: Lens' FrontendState SimulationBottomPanelView
_simulationBottomPanelView = _Newtype <<< prop (SProxy :: SProxy "simulationBottomPanelView")

_helpContext :: Lens' FrontendState HelpContext
_helpContext = _Newtype <<< prop (SProxy :: SProxy "helpContext")

_editorPreferences :: Lens' FrontendState Editor.Preferences
_editorPreferences = _Newtype <<< prop (SProxy :: SProxy "editorPreferences")

_compilationResult :: Lens' FrontendState (WebData (JsonEither InterpreterError (InterpreterResult RunResult)))
_compilationResult = _Newtype <<< prop (SProxy :: SProxy "compilationResult")

_marloweCompileResult :: Lens' FrontendState (Either (Array MarloweError) Unit)
_marloweCompileResult = _Newtype <<< prop (SProxy :: SProxy "marloweCompileResult")

_authStatus :: Lens' FrontendState (WebData AuthStatus)
_authStatus = _Newtype <<< prop (SProxy :: SProxy "authStatus")

_createGistResult :: Lens' FrontendState (WebData Gist)
_createGistResult = _Newtype <<< prop (SProxy :: SProxy "createGistResult")

_loadGistResult :: Lens' FrontendState (Either String (WebData Gist))
_loadGistResult = _Newtype <<< prop (SProxy :: SProxy "loadGistResult")

_gistUrl :: Lens' FrontendState (Maybe String)
_gistUrl = _Newtype <<< prop (SProxy :: SProxy "gistUrl")

_marloweState :: Lens' FrontendState (NonEmptyList MarloweState)
_marloweState = _Newtype <<< prop (SProxy :: SProxy "marloweState")

_oldContract :: Lens' FrontendState (Maybe String)
_oldContract = _Newtype <<< prop (SProxy :: SProxy "oldContract")

_blocklyState :: Lens' FrontendState (Maybe BlocklyState)
_blocklyState = _Newtype <<< prop (SProxy :: SProxy "blocklyState")

_analysisState :: Lens' FrontendState (RemoteData String Result)
_analysisState = _Newtype <<< prop (SProxy :: SProxy "analysisState")

_selectedHole :: Lens' FrontendState (Maybe String)
_selectedHole = _Newtype <<< prop (SProxy :: SProxy "selectedHole")

_showRightPanel :: Lens' FrontendState Boolean
_showRightPanel = _Newtype <<< prop (SProxy :: SProxy "showRightPanel")

_showBottomPanel :: Lens' FrontendState Boolean
_showBottomPanel = _Newtype <<< prop (SProxy :: SProxy "showBottomPanel")

_showErrorDetail :: Lens' FrontendState Boolean
_showErrorDetail = _Newtype <<< prop (SProxy :: SProxy "showErrorDetail")

-- editable
_timestamp ::
  forall s a.
  Lens' { timestamp :: a | s } a
_timestamp = prop (SProxy :: SProxy "timestamp")

_value :: forall s a. Lens' { value :: a | s } a
_value = prop (SProxy :: SProxy "value")

data ActionInputId
  = DepositInputId AccountId Party Token BigInteger
  | ChoiceInputId ChoiceId (Array Bound)
  | NotifyInputId

derive instance eqActionInputId :: Eq ActionInputId

derive instance ordActionInputId :: Ord ActionInputId

type MarloweState
  = { possibleActions :: Map (Maybe PubKey) (Map ActionInputId ActionInput)
    , pendingInputs :: Array (Tuple Input (Maybe PubKey))
    , transactionError :: Maybe TransactionError
    , transactionWarnings :: Array TransactionWarning
    , state :: State
    , slot :: Slot
    , moneyInContract :: Assets
    , contract :: Maybe Contract
    , editorErrors :: Array IMarker
    , editorWarnings :: Array IMarker
    , holes :: Holes
    , payments :: Array Payment
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

_payments :: forall s a. Lens' { payments :: a | s } a
_payments = prop (SProxy :: SProxy "payments")

_currentMarloweState :: Lens' FrontendState MarloweState
_currentMarloweState = _marloweState <<< _Head

_currentContract :: Lens' FrontendState (Maybe Contract)
_currentContract = _currentMarloweState <<< _contract

emptyMarloweState :: Slot -> MarloweState
emptyMarloweState sn =
  { possibleActions: mempty
  , pendingInputs: mempty
  , transactionError: Nothing
  , transactionWarnings: []
  , state: emptyState sn
  , slot: zero
  , moneyInContract: mempty
  , contract: Nothing
  , editorErrors: mempty
  , editorWarnings: mempty
  , holes: mempty
  , payments: []
  }

type WebData
  = RemoteData AjaxError

-- | On the front end we need Actions however we also need to keep track of the current
-- | choice that has been set for Choices
data ActionInput
  = DepositInput AccountId Party Token BigInteger
  | ChoiceInput ChoiceId (Array Bound) ChosenNum
  | NotifyInput

minimumBound :: Array Bound -> ChosenNum
minimumBound bnds = case uncons (map boundFrom bnds) of
  Just { head, tail } -> foldl1 min (head :| tail)
  Nothing -> zero

actionToActionInput :: State -> Action -> Tuple ActionInputId ActionInput
actionToActionInput state (Deposit accountId party token value) =
  let
    minSlot = state ^. _minSlot

    evalResult = evalValue env state value

    env = Environment { slotInterval: (SlotInterval minSlot minSlot) }
  in
    Tuple (DepositInputId accountId party token evalResult) (DepositInput accountId party token evalResult)

actionToActionInput _ (Choice choiceId bounds) = Tuple (ChoiceInputId choiceId bounds) (ChoiceInput choiceId bounds (minimumBound bounds))

actionToActionInput _ (Notify _) = Tuple NotifyInputId NotifyInput

data HelpContext
  = MarloweHelp
  | InputComposerHelp
  | TransactionComposerHelp

derive instance genericHelpContext :: Generic HelpContext _

instance showHelpContext :: Show HelpContext where
  show = genericShow
