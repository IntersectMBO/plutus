module Types where

import Prelude
import Semantics
import Data.BigInt
import API
  ( RunResult
  )
import Ace.Halogen.Component
  ( AceMessage
  , AceQuery
  )
import Auth
  ( AuthStatus
  )
import Control.Comonad
  ( class Comonad
  , extract
  )
import Control.Extend
  ( class Extend
  , extend
  )
import DOM.HTML.Event.Types
  ( DragEvent
  )
import Data.Either
  ( Either
  )
import Data.Functor.Coproduct
  ( Coproduct(..)
  )
import Data.Generic
  ( class Generic
  , gShow
  )
import Data.Lens
  ( Lens'
  , Prism'
  , Lens
  , _2
  , over
  , prism'
  , traversed
  , view
  )
import Data.Lens.Iso.Newtype
  ( _Newtype
  )
import Data.Lens.Record
  ( prop
  )
import Data.Map
  ( Map
  )
import Data.Maybe
  ( Maybe(..)
  )
import Data.Symbol
  ( SProxy(..)
  )
import Data.Tuple
  ( Tuple(..)
  )
import Gist
  ( Gist
  )
import Halogen.Component.ChildPath
  ( ChildPath
  , cpL
  , cpR
  )
import Language.Haskell.Interpreter
  ( CompilationError
  )
import Network.RemoteData
  ( RemoteData
  )
import Servant.PureScript.Affjax
  ( AjaxError
  )
import Type.Data.Boolean
  ( kind Boolean
  )

import Data.Array as Array

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
  | ScrollTo {row :: Int, column :: Int} a
  | LoadMarloweScript String a
  | SetSignature {person :: Person, isChecked :: Boolean} a
  | ApplyTrasaction a
  | NextBlock a
  | CompileMarlowe a

------------------------------------------------------------
type ChildQuery
  = Coproduct AceQuery AceQuery

type ChildSlot
  = Either EditorSlot MarloweEditorSlot

data EditorSlot
  = EditorSlot

derive instance eqComponentEditorSlot ::
  Eq EditorSlot

derive instance ordComponentEditorSlot ::
  Ord EditorSlot

data MarloweEditorSlot
  = MarloweEditorSlot

derive instance eqComponentMarloweEditorSlot ::
  Eq MarloweEditorSlot

derive instance ordComponentMarloweEditorSlot ::
  Ord MarloweEditorSlot

cpEditor ::
  ChildPath AceQuery ChildQuery EditorSlot ChildSlot
cpEditor = cpL

cpMarloweEditor ::
  ChildPath AceQuery ChildQuery MarloweEditorSlot ChildSlot
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
  = {view :: View, runResult :: RemoteData AjaxError (Either (Array CompilationError) RunResult), marloweCompileResult :: Either (Array MarloweError) Unit, authStatus :: RemoteData AjaxError AuthStatus, createGistResult :: RemoteData AjaxError Gist, marloweState :: MarloweState}

data MarloweError
  = MarloweError String

_view ::
  forall s a.
  Lens' {view :: a | s} a
_view = prop (SProxy :: SProxy "view")

_runResult ::
  forall s a.
  Lens' {runResult :: a | s} a
_runResult = prop (SProxy :: SProxy "runResult")

_authStatus ::
  forall s a.
  Lens' {authStatus :: a | s} a
_authStatus = prop (SProxy :: SProxy "authStatus")

_createGistResult ::
  forall s a.
  Lens' {createGistResult :: a | s} a
_createGistResult = prop (SProxy :: SProxy "createGistResult")

_marloweState ::
  forall s a.
  Lens' {marloweState :: a | s} a
_marloweState = prop (SProxy :: SProxy "marloweState")


-- Oracles should not be grouped (only one line per oracle) like:
--    Oracle 3: Provide value [$value] for block [$timestamp]
type OracleEntry = { timestamp :: BlockNumber -- editable
                   , value :: BigInt }        -- editable

_timestamp ::
  forall s a.
  Lens' {timestamp :: a | s} a
_timestamp = prop (SProxy :: SProxy "timestamp")

_value ::
  forall s a.
  Lens' {value :: a | s} a
_value = prop (SProxy :: SProxy "value")

type InputData = { oracleData :: Map IdOracle OracleEntry -- oracle inputs (before person
                 , inputs :: Map Person PersonInput } -- inputs (grouped by Person id)

_oracleData ::
  forall s a.
  Lens' {oracleData :: a | s} a
_oracleData = prop (SProxy :: SProxy "oracleData")

_inputs ::
  forall s a.
  Lens' {inputs :: a | s} a
_inputs = prop (SProxy :: SProxy "inputs")

type TransactionData = { inputs :: Array (Either (Tuple Person PersonInput) (Tuple IdOracle OracleEntry))
                                  -- ^ not grouped (but participants and oracles labelled inline)
                                  -- e.g: Participant 1 - Action $IdAction - Commit ....
                                  --      Oracle 3 - Provide value $value for block $timestamp
                       , signatures :: Map Person Boolean -- checkboxes
                       , outcomes :: Map Person BigInt } -- table under checkboxes

_signatures ::
  forall s a.
  Lens' {signatures :: a | s} a
_signatures = prop (SProxy :: SProxy "signatures")

_outcomes ::
  forall s a.
  Lens' {outcomes :: a | s} a
_outcomes = prop (SProxy :: SProxy "outcomes")

data PersonInput =
   CommitAction IdAction IdCommit Value Timeout -- "Action $IdAction: Commit $Value ADA with id $IdCommit until block $Timeout"
 | PayClaim IdAction IdCommit Value -- "Action $IdAction: Claim a payment of $Value ADA from commit $IdCommit"
 | ProvideChoice IdChoice Choice -- "Choice $IdChoice: Choose value [$Choice]"


type MarloweState = { input :: InputData
                    , transaction :: TransactionData
                    , state :: State
                    , blockNum :: BlockNumber
		    , contract :: Contract
                    }

_input ::
  forall s a.
  Lens' {input :: a | s} a
_input = prop (SProxy :: SProxy "input")

_transaction ::
  forall s a.
  Lens' {transaction :: a | s} a
_transaction = prop (SProxy :: SProxy "transaction")

_state ::
  forall s a.
  Lens' {state :: a | s} a
_state = prop (SProxy :: SProxy "state")

_blockNum ::
  forall s a.
  Lens' {blockNum :: a | s} a
_blockNum = prop (SProxy :: SProxy "blockNum")

_contract ::
  forall s a.
  Lens' {contract :: a | s} a
_contract = prop (SProxy :: SProxy "contract")

