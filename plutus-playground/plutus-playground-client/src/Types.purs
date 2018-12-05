module Types where

import Ace.Halogen.Component (AceMessage, AceQuery)
import Control.Comonad (class Comonad, extract)
import Control.Extend (class Extend, extend)
import Data.Array as Array
import Data.Either (Either)
import Data.Either.Nested (Either3)
import Data.Functor.Coproduct.Nested (Coproduct3)
import Data.Generic (class Generic)
import Data.Lens (Lens', Prism', _2, over, prism', traversed, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Halogen.Component.ChildPath (ChildPath, cp1, cp2, cp3)
import Halogen.ECharts (EChartsMessage, EChartsQuery)
import Network.RemoteData (RemoteData)
import Playground.API (CompilationError, EvaluationResult, FunctionSchema, SimpleArgumentSchema(SimpleObjectArgument, UnknownArgument, SimpleStringArgument, SimpleIntArgument), _FunctionSchema)
import Prelude (class Eq, class Functor, class Ord, class Show, show, ($), (<$>), (<<<), (<>))
import Servant.PureScript.Affjax (AjaxError)
import Wallet.Emulator.Types (Wallet)
import Ledger.Types (Tx)

-- | A mock wallet combines an actual Plutus wallet record with a
-- | pretend opening balance.
newtype MockWallet = MockWallet
  { wallet :: Wallet
  , balance :: Int
  }
derive instance genericMockWallet :: Generic MockWallet
derive instance newtypeMockWallet :: Newtype MockWallet _

_MockWallet :: forall a. Newtype MockWallet a => Lens' MockWallet a
_MockWallet = _Newtype

_wallet :: forall s a. Lens' {wallet :: a | s} a
_wallet = prop (SProxy :: SProxy "wallet")

_balance :: forall s a. Lens' {balance :: a | s} a
_balance = prop (SProxy :: SProxy "balance")

------------------------------------------------------------

data Action
  = Action
      { mockWallet :: MockWallet
      , functionSchema :: FunctionSchema SimpleArgument
      }
  | Wait { blocks :: Int }

_Action ::
  Prism'
    Action
    { mockWallet :: MockWallet
    , functionSchema :: FunctionSchema SimpleArgument
    }
_Action = prism' Action f
  where
    f (Action r) = Just r
    f _ = Nothing

_Wait ::
  Prism'
    Action
    { blocks :: Int
    }
_Wait = prism' Wait f
  where
    f (Wait r) = Just r
    f _ = Nothing

_functionSchema :: forall a r. Lens'{ functionSchema :: a | r} a
_functionSchema = prop (SProxy :: SProxy "functionSchema")

_argumentSchema :: forall a r. Lens'{ argumentSchema :: a | r} a
_argumentSchema = prop (SProxy :: SProxy "argumentSchema")

_blocks :: forall a r. Lens'{ blocks :: a | r} a
_blocks = prop (SProxy :: SProxy "blocks")

------------------------------------------------------------

data ValidationError
  = Required String
  | Unsupported String

derive instance eqValidationError :: Eq ValidationError

instance showValidationError :: Show ValidationError where
  show (Required path) = path <> " is required."
  show (Unsupported path) = path <> " is unsupported."

addPath :: String -> ValidationError -> ValidationError
addPath path (Required subpath) = Required $ path <> "." <> subpath
addPath path (Unsupported subpath) = Unsupported $ path <> "." <> subpath

validate :: Action -> Array ValidationError
validate (Wait _) = []
validate (Action action) =
  Array.concat $ Array.mapWithIndex (validateArgument <<< show) args
  where
    args :: Array SimpleArgument
    args = view (_functionSchema <<< _FunctionSchema <<< _argumentSchema) action

validateArgument :: forall a. String -> SimpleArgument -> Array ValidationError
validateArgument path Unknowable = [ Unsupported path ]
validateArgument path (SimpleInt Nothing) = [ Required path ]
validateArgument path (SimpleInt (Just _)) = []
validateArgument path (SimpleString Nothing) = [ Required path ]
validateArgument path (SimpleString (Just _)) = []
validateArgument path (SimpleObject subArguments) =
  Array.concat $
    (\(Tuple name subArgument) -> addPath path <$> validateArgument name subArgument)
    <$>
    subArguments

------------------------------------------------------------

data Query a
  = HandleEditorMessage AceMessage a
  | HandleMockchainChartMessage EChartsMessage a
  | HandleBalancesChartMessage EChartsMessage a
  | CompileProgram a
  | ScrollTo { row :: Int, column :: Int } a
  | AddWallet a
  | RemoveWallet Int a
  | AddAction Action a
  | SetBalance Wallet Int a
  | AddWaitAction Int a
  | RemoveAction Int a
  | EvaluateActions a
  | PopulateAction Int Int (FormEvent a)
  | SetWaitTime Int Int a

data FormEvent a
  = SetIntField Int a
  | SetStringField String a
  | SetSubField Int (FormEvent a)

derive instance functorFormEvent :: Functor FormEvent

instance extendFormEvent :: Extend FormEvent where
  extend f event@(SetIntField n _) = SetIntField n $ f event
  extend f event@(SetStringField s _) = SetStringField s $ f event
  extend f event@(SetSubField n _) = SetSubField n $ extend f event


instance comonadFormEvent :: Comonad FormEvent where
  extract (SetIntField _ a) = a
  extract (SetStringField _ a) = a
  extract (SetSubField _ e) = extract e

------------------------------------------------------------

type ChildQuery = Coproduct3 AceQuery EChartsQuery EChartsQuery
type ChildSlot = Either3 EditorSlot MockchainChartSlot BalancesChartSlot

data EditorSlot = EditorSlot
derive instance eqComponentEditorSlot :: Eq EditorSlot
derive instance ordComponentEditorSlot :: Ord EditorSlot

data MockchainChartSlot = MockchainChartSlot
derive instance eqComponentMockchainChartSlot :: Eq MockchainChartSlot
derive instance ordComponentMockchainChartSlot :: Ord MockchainChartSlot

data BalancesChartSlot = BalancesChartSlot
derive instance eqComponentBalancesChartSlot :: Eq BalancesChartSlot
derive instance ordComponentBalancesChartSlot :: Ord BalancesChartSlot

cpEditor :: ChildPath AceQuery ChildQuery EditorSlot ChildSlot
cpEditor = cp1

cpMockchainChart :: ChildPath EChartsQuery ChildQuery MockchainChartSlot ChildSlot
cpMockchainChart = cp2

cpBalancesChart :: ChildPath EChartsQuery ChildQuery BalancesChartSlot ChildSlot
cpBalancesChart = cp3

-----------------------------------------------------------

type CompilationResult =
  Either (Array CompilationError) (Array (FunctionSchema SimpleArgumentSchema))

type Blockchain = Array (Array Tx)

type State =
  { editorContents :: String
  , compilationResult :: RemoteData AjaxError CompilationResult
  , wallets :: Array MockWallet
  , actions :: Array Action
  , evaluationResult :: RemoteData AjaxError EvaluationResult
  }

_actions :: forall s a. Lens' {actions :: a | s} a
_actions = prop (SProxy :: SProxy "actions")

_wallets :: forall s a. Lens' {wallets :: a | s} a
_wallets = prop (SProxy :: SProxy "wallets")

_evaluationResult :: forall s a. Lens' {evaluationResult :: a | s} a
_evaluationResult = prop (SProxy :: SProxy "evaluationResult")

_editorContents :: forall s a. Lens' {editorContents :: a | s} a
_editorContents = prop (SProxy :: SProxy "editorContents")

_compilationResult :: forall s a. Lens' {compilationResult :: a | s} a
_compilationResult = prop (SProxy :: SProxy "compilationResult")

------------------------------------------------------------

data SimpleArgument
  = SimpleInt (Maybe Int)
  | SimpleString (Maybe String)
  | SimpleObject (Array (Tuple String SimpleArgument))
  | Unknowable

toValue :: SimpleArgumentSchema -> SimpleArgument
toValue SimpleIntArgument = SimpleInt Nothing
toValue SimpleStringArgument = SimpleString Nothing
toValue (SimpleObjectArgument fields) = SimpleObject (over (traversed <<< _2) toValue fields)
toValue (UnknownArgument _) = Unknowable

-- | This should just be `map` but we can't put an orphan instance on FunctionSchema. :-(
toValueLevel :: FunctionSchema SimpleArgumentSchema -> FunctionSchema SimpleArgument
toValueLevel = over (_Newtype <<< prop (SProxy :: SProxy "argumentSchema") <<< traversed) toValue
