module Types where

import API (RunResult)
import Ace.Halogen.Component (AceMessage, AceQuery)
import Auth (AuthStatus)
import Data.BigInteger (BigInteger)
import Data.Either (Either)
import Data.Functor.Coproduct (Coproduct)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens, Lens', lens)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.RawJson (JsonEither)
import Data.Symbol (SProxy(..))
import Gist (Gist)
import Halogen.Component.ChildPath (ChildPath, cpL, cpR)
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult)
import Marlowe.Semantics (DetachedPrimitiveWIA, AnyInput, State, ErrorResult, DynamicProblem)
import Marlowe.Types (BlockNumber, Choice, Contract, IdChoice, IdOracle, Person)
import Network.RemoteData (RemoteData)
import Prelude (class Eq, class Ord, class Show, Unit, (<<<))
import Servant.PureScript.Ajax (AjaxError)
import Type.Data.Boolean (kind Boolean)
import Web.HTML.Event.DragEvent (DragEvent)

_Head :: forall a. Lens (NonEmptyList a) (NonEmptyList a) a a
_Head = lens NEL.head (\l new -> let {head, tail} = NEL.uncons l in NEL.cons' new tail)

------------------------------------------------------------
data Query a
  -- Haskell Editor
  = HandleEditorMessage AceMessage a
  | HandleDragEvent DragEvent a
  | HandleDropEvent DragEvent a
  | MarloweHandleEditorMessage AceMessage a
  | MarloweHandleDragEvent DragEvent a
  | MarloweHandleDropEvent DragEvent a
  -- Gist support.
  | CheckAuthStatus a
  | PublishGist a
  | SetGistUrl String a
  | LoadGist a
  -- haskell actions
  | ChangeView View a
  | LoadScript String a
  | CompileProgram a
  | SendResult a
  | ScrollTo {row :: Int, column :: Int} a
  | LoadMarloweScript String a
  -- marlowe actions
  | SetSignature {person :: Person, isChecked :: Boolean} a
  | ApplyTransaction a
  | NextBlock a
  | AddAnyInput {person :: Maybe Person, anyInput :: AnyInput} a
  | RemoveAnyInput AnyInput a
  | SetChoice {idChoice :: IdChoice, value :: Choice} a
  | SetOracleVal {idOracle :: IdOracle, value :: BigInteger} a
  | SetOracleBn {idOracle :: IdOracle, blockNumber :: BlockNumber} a
  | ResetSimulator a
  | Undo a

------------------------------------------------------------
type ChildQuery
  = Coproduct AceQuery AceQuery

type ChildSlot
  = Either EditorSlot MarloweEditorSlot

data EditorSlot
  = EditorSlot

derive instance eqComponentEditorSlot :: Eq EditorSlot

derive instance ordComponentEditorSlot :: Ord EditorSlot

data MarloweEditorSlot
  = MarloweEditorSlot

derive instance eqComponentMarloweEditorSlot :: Eq MarloweEditorSlot

derive instance ordComponentMarloweEditorSlot :: Ord MarloweEditorSlot

cpEditor :: ChildPath AceQuery ChildQuery EditorSlot ChildSlot
cpEditor = cpL

cpMarloweEditor :: ChildPath AceQuery ChildQuery MarloweEditorSlot ChildSlot
cpMarloweEditor = cpR

-----------------------------------------------------------
data View
  = Editor
  | Simulation

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

-- Oracles should not be grouped (only one line per oracle) like:
--    Oracle 3: Provide value [$value] for block [$timestamp]
type OracleEntry
  = {blockNumber :: BlockNumber, value :: BigInteger}

-- editable
_timestamp ::
  forall s a.
  Lens' {timestamp :: a | s} a
_timestamp = prop (SProxy :: SProxy "timestamp")

_value :: forall s a. Lens' {value :: a | s} a
_value = prop (SProxy :: SProxy "value")

type InputData
  = { inputs :: Map Person (List DetachedPrimitiveWIA)
  , choiceData :: Map Person (Map BigInteger Choice)
  , oracleData :: Map IdOracle OracleEntry
  }

_inputs :: forall s a. Lens' {inputs :: a | s} a
_inputs = prop (SProxy :: SProxy "inputs")

_choiceData :: forall s a. Lens' {choiceData :: a | s} a
_choiceData = prop (SProxy :: SProxy "choiceData")

_oracleData ::
  forall s a.
  Lens' {oracleData :: a | s} a
_oracleData = prop (SProxy :: SProxy "oracleData")

data TransactionValidity
  = EmptyTransaction
  | ValidTransaction (List DynamicProblem)
  | InvalidTransaction ErrorResult

derive instance eqTransactionValidity :: Eq TransactionValidity

derive instance ordTransactionValidity :: Ord TransactionValidity

isValidTransaction :: TransactionValidity -> Boolean
isValidTransaction (ValidTransaction _) = true

isValidTransaction _ = false

isInvalidTransaction :: TransactionValidity -> Boolean
isInvalidTransaction (InvalidTransaction _) = true

isInvalidTransaction _ = false

type TransactionData
  = {inputs :: Array AnyInput, signatures :: Map Person Boolean, outcomes :: Map Person BigInteger, validity :: TransactionValidity}

-- table under checkboxes
_signatures ::
  forall s a.
  Lens' {signatures :: a | s} a
_signatures = prop (SProxy :: SProxy "signatures")

_outcomes :: forall s a. Lens' {outcomes :: a | s} a
_outcomes = prop (SProxy :: SProxy "outcomes")

_validity :: forall s a. Lens' {validity :: a | s} a
_validity = prop (SProxy :: SProxy "validity")

-- "Choice $IdChoice: Choose value [$Choice]"
type MarloweState
  = { input :: InputData
  , transaction :: TransactionData
  , state :: State
  , blockNum :: BlockNumber
  , moneyInContract :: BigInteger
  , contract :: Maybe Contract
  }

_input :: forall s a. Lens' {input :: a | s} a
_input = prop (SProxy :: SProxy "input")

_transaction :: forall s a. Lens' {transaction :: a | s} a
_transaction = prop (SProxy :: SProxy "transaction")

_state :: forall s a. Lens' {state :: a | s} a
_state = prop (SProxy :: SProxy "state")

_blockNum :: forall s a. Lens' {blockNum :: a | s} a
_blockNum = prop (SProxy :: SProxy "blockNum")

_moneyInContract :: forall s a. Lens' {moneyInContract :: a | s} a
_moneyInContract = prop (SProxy :: SProxy "moneyInContract")

_contract :: forall s a. Lens' {contract :: a | s} a
_contract = prop (SProxy :: SProxy "contract")

--- Language.Haskell.Interpreter ---
_result :: forall s a. Lens' {result :: a | s} a
_result = prop (SProxy :: SProxy "result")

_warnings :: forall s a. Lens' {warnings :: a | s} a
_warnings = prop (SProxy :: SProxy "warnings")

_currentMarloweState :: Lens' FrontendState MarloweState
_currentMarloweState = _marloweState <<< _Head

_currentContract :: Lens' FrontendState (Maybe Contract)
_currentContract = _currentMarloweState <<< _contract

_currentTransaction :: Lens' FrontendState TransactionData
_currentTransaction = _currentMarloweState <<< _transaction

_currentInput :: Lens' FrontendState InputData
_currentInput = _currentMarloweState <<< _input

type WebData
  = RemoteData AjaxError
