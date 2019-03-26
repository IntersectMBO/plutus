module Types where

import API (RunResult)
import Ace.Halogen.Component (AceMessage, AceQuery)
import Auth (AuthStatus)
import DOM.HTML.Event.Types (DragEvent)
import Data.BigInteger (BigInteger)
import Data.Either (Either)
import Data.Functor.Coproduct (Coproduct)
import Data.Generic (class Generic, gShow)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Gist (Gist)
import Halogen.Component.ChildPath (ChildPath, cpL, cpR)
import Language.Haskell.Interpreter (CompilationError)
import Marlowe.Types (BlockNumber, Choice, Contract, IdChoice, IdOracle, Person)
import Network.RemoteData (RemoteData)
import Prelude (class Eq, class Ord, class Show, Unit)
import Semantics (DetachedPrimitiveWIA, AnyInput, State, ErrorResult, DynamicProblem)
import Servant.PureScript.Affjax (AjaxError)
import Type.Data.Boolean (kind Boolean)

------------------------------------------------------------
data Query a
  = HandleEditorMessage AceMessage a
  | HandleDragEvent DragEvent a
  | HandleDropEvent DragEvent a
  | MarloweHandleEditorMessage AceMessage a
  | MarloweHandleDragEvent DragEvent a
  | MarloweHandleDropEvent DragEvent a
  | CheckAuthStatus a
  | PublishGist a
  | ChangeView View a
  | LoadScript String a
  | CompileProgram a
  | SendResult a
  | ScrollTo {row :: Int, column :: Int} a
  | LoadMarloweScript String a
  | SetSignature {person :: Person, isChecked :: Boolean} a
  | ApplyTransaction a
  | NextBlock a
  | AddAnyInput {person :: Maybe Person, anyInput :: AnyInput} a
  | RemoveAnyInput AnyInput a
  | SetChoice {idChoice :: IdChoice, value :: Choice} a
  | SetOracleVal {idOracle :: IdOracle, value :: BigInteger} a
  | SetOracleBn {idOracle :: IdOracle, blockNumber :: BlockNumber} a
  | ResetSimulator a

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

derive instance genericView :: Generic View

instance showView :: Show View where
  show = gShow

type FrontendState
  = {view :: View, runResult :: RemoteData AjaxError (Either (Array CompilationError) RunResult), marloweCompileResult :: Either (Array MarloweError) Unit, authStatus :: RemoteData AjaxError AuthStatus, createGistResult :: RemoteData AjaxError Gist, marloweState :: MarloweState, oldContract :: Maybe String}

data MarloweError
  = MarloweError String

_view :: forall s a. Lens' {view :: a | s} a
_view = prop (SProxy :: SProxy "view")

_runResult :: forall s a. Lens' {runResult :: a | s} a
_runResult = prop (SProxy :: SProxy "runResult")

_marloweCompileResult :: forall s a. Lens' {marloweCompileResult :: a | s} a
_marloweCompileResult = prop (SProxy :: SProxy "marloweCompileResult")

_authStatus :: forall s a. Lens' {authStatus :: a | s} a
_authStatus = prop (SProxy :: SProxy "authStatus")

_createGistResult :: forall s a. Lens' {createGistResult :: a | s} a
_createGistResult = prop (SProxy :: SProxy "createGistResult")

_marloweState :: forall s a. Lens' {marloweState :: a | s} a
_marloweState = prop (SProxy :: SProxy "marloweState")

_oldContract :: forall s a. Lens' {oldContract :: a | s} a
_oldContract = prop (SProxy :: SProxy "oldContract")

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

data TransactionValidity = EmptyTransaction
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
        = {input :: InputData, transaction :: TransactionData, state :: State, blockNum :: BlockNumber, moneyInContract :: BigInteger, contract :: Maybe Contract}

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

