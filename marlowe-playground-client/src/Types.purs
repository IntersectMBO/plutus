module Types where

import API (RunResult)
import Ace (Annotation)
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
import Gist (Gist)
import Halogen as H
import Halogen.Blockly (BlocklyQuery, BlocklyMessage)
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult)
import Marlowe.Semantics (AccountId, Action(..), Ada, Bound, ChoiceId, ChosenNum, Contract, Environment(..), Input, Observation, Party, Payment, PubKey, Slot, SlotInterval(..), State, TransactionError, _minSlot, boundFrom, emptyState, evalValue)
import Marlowe.Symbolic.Types.Response (Result)
import Network.RemoteData (RemoteData)
import Prelude (class Eq, class Ord, class Show, Unit, map, mempty, min, zero, (<<<))
import Servant.PureScript.Ajax (AjaxError)
import Type.Data.Boolean (kind Boolean)
import Web.HTML.Event.DragEvent (DragEvent)

_Head :: forall a. Lens (NonEmptyList a) (NonEmptyList a) a a
_Head = lens NEL.head (\l new -> let { head, tail } = NEL.uncons l in NEL.cons' new tail)

------------------------------------------------------------
data HQuery a
  = ReceiveWebsocketMessage String a

data HAction
  -- Haskell Editor
  = HandleEditorMessage AceMessage
  | HandleDragEvent DragEvent
  | HandleDropEvent DragEvent
  | MarloweHandleEditorMessage AceMessage
  | MarloweHandleDragEvent DragEvent
  | MarloweHandleDropEvent DragEvent
  -- Gist support.
  | CheckAuthStatus
  | PublishGist
  | SetGistUrl String
  | LoadGist
  -- haskell actions
  | ChangeView View
  | LoadScript String
  | CompileProgram
  | SendResult
  | ScrollTo { row :: Int, column :: Int }
  | LoadMarloweScript String
  -- marlowe actions
  | ApplyTransaction
  | NextSlot
  | AddInput PubKey Input (Array Bound)
  | RemoveInput PubKey Input
  | SetChoice ChoiceId ChosenNum
  | ResetSimulator
  | Undo
  -- blockly
  | HandleBlocklyMessage BlocklyMessage
  | SetBlocklyCode
  -- websocket
  | AnalyseContract

data WebsocketMessage = WebsocketMessage String

------------------------------------------------------------
type ChildSlots =
  ( editorSlot :: H.Slot AceQuery AceMessage Unit
  , marloweEditorSlot :: H.Slot AceQuery AceMessage Unit
  , blocklySlot :: H.Slot BlocklyQuery BlocklyMessage Unit
  )

_editorSlot :: SProxy "editorSlot"
_editorSlot = SProxy

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

newtype FrontendState
  = FrontendState
  { view :: View
  , compilationResult :: WebData (JsonEither InterpreterError (InterpreterResult RunResult))
  , marloweCompileResult :: Either (Array MarloweError) Unit
  , authStatus :: WebData AuthStatus
  , createGistResult :: WebData Gist
  , gistUrl :: Maybe String
  , marloweState :: NonEmptyList MarloweState
  , oldContract :: Maybe String
  , blocklyState :: Maybe BlocklyState
  , analysisState :: RemoteData String Result
  }

derive instance newtypeFrontendState :: Newtype FrontendState _

data MarloweError
  = MarloweError String

_view :: Lens' FrontendState View
_view = _Newtype <<< prop (SProxy :: SProxy "view")

_compilationResult :: Lens' FrontendState (WebData (JsonEither InterpreterError (InterpreterResult RunResult)))
_compilationResult = _Newtype <<< prop (SProxy :: SProxy "compilationResult")

_marloweCompileResult :: Lens' FrontendState (Either (Array MarloweError) Unit)
_marloweCompileResult = _Newtype <<< prop (SProxy :: SProxy "marloweCompileResult")

_authStatus :: Lens' FrontendState (WebData AuthStatus)
_authStatus = _Newtype <<< prop (SProxy :: SProxy "authStatus")

_createGistResult :: Lens' FrontendState (WebData Gist)
_createGistResult = _Newtype <<< prop (SProxy :: SProxy "createGistResult")

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

-- editable
_timestamp ::
  forall s a.
  Lens' { timestamp :: a | s } a
_timestamp = prop (SProxy :: SProxy "timestamp")

_value :: forall s a. Lens' { value :: a | s } a
_value = prop (SProxy :: SProxy "value")

data ActionInputId
  = DepositInputId AccountId Party
  | ChoiceInputId ChoiceId (Array Bound)
  | NotifyInputId Observation

derive instance eqActionInputId :: Eq ActionInputId

derive instance ordActionInputId :: Ord ActionInputId

type MarloweState
  = { possibleActions :: Map PubKey (Map ActionInputId ActionInput)
    , pendingInputs :: Array (Tuple Input PubKey)
    , transactionError :: Maybe TransactionError
    , state :: State
    , slot :: Slot
    , moneyInContract :: Ada
    , contract :: Maybe Contract
    , editorErrors :: Array Annotation
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

_slot :: forall s a. Lens' { slot :: a | s } a
_slot = prop (SProxy :: SProxy "slot")

_moneyInContract :: forall s a. Lens' { moneyInContract :: a | s } a
_moneyInContract = prop (SProxy :: SProxy "moneyInContract")

_contract :: forall s a. Lens' { contract :: a | s } a
_contract = prop (SProxy :: SProxy "contract")

_editorErrors :: forall s a. Lens' { editorErrors :: a | s } a
_editorErrors = prop (SProxy :: SProxy "editorErrors")

--- Language.Haskell.Interpreter ---
_result :: forall s a. Lens' { result :: a | s } a
_result = prop (SProxy :: SProxy "result")

_warnings :: forall s a. Lens' { warnings :: a | s } a
_warnings = prop (SProxy :: SProxy "warnings")

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
  , state: emptyState sn
  , slot: zero
  , moneyInContract: zero
  , contract: Nothing
  , editorErrors: []
  , payments: []
  }
type WebData
  = RemoteData AjaxError

-- | On the front end we need Actions however we also need to keep track of the current
-- | choice that has been set for Choices
data ActionInput
  = DepositInput AccountId Party BigInteger
  | ChoiceInput ChoiceId (Array Bound) ChosenNum
  | NotifyInput Observation

minimumBound :: Array Bound -> ChosenNum
minimumBound bnds =
  case uncons (map boundFrom bnds) of
    Just { head, tail } -> foldl1 min (head :| tail)
    Nothing -> zero

actionToActionInput :: State -> Action -> Tuple ActionInputId ActionInput
actionToActionInput state (Deposit accountId party value) =
  let minSlot = state ^. _minSlot
      env = Environment { slotInterval: (SlotInterval minSlot minSlot) }
  in Tuple (DepositInputId accountId party) (DepositInput accountId party (evalValue env state value))
actionToActionInput _ (Choice choiceId bounds) = Tuple (ChoiceInputId choiceId bounds) (ChoiceInput choiceId bounds (minimumBound bounds))
actionToActionInput _ (Notify observation) = Tuple (NotifyInputId observation) (NotifyInput observation)
