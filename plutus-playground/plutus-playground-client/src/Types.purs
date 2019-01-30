module Types where

import Ace.Halogen.Component (AceMessage, AceQuery)
import Control.Comonad (class Comonad, extract)
import Control.Extend (class Extend, extend)
import DOM.HTML.Event.Types (DragEvent)
import Data.Array as Array
import Data.Either (Either)
import Data.Either.Nested (Either3)
import Data.Functor.Coproduct.Nested (Coproduct3)
import Data.Generic (class Generic, gShow)
import Data.Lens (Lens', Prism', Lens, _2, over, prism', traversed, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Halogen.Component.ChildPath (ChildPath, cp1, cp2, cp3)
import Halogen.ECharts (EChartsMessage, EChartsQuery)
import Ledger.Types (Tx)
import Network.RemoteData (RemoteData)
import Playground.API (CompilationError, CompilationResult, EvaluationResult, FunctionSchema, SimpleArgumentSchema(SimpleObjectArgument, UnknownArgument, SimpleStringArgument, SimpleIntArgument), _FunctionSchema)
import Prelude (class Eq, class Functor, class Ord, class Show, Unit, show, ($), (<$>), (<<<), (<>))
import Servant.PureScript.Affjax (AjaxError)
import Wallet.Emulator.Types (Wallet)

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

derive instance genericAction :: Generic Action

instance showAction :: Show Action where
  show = gShow

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

_functionSchema :: forall a b r. Lens { functionSchema :: a | r} { functionSchema :: b | r} a b
_functionSchema = prop (SProxy :: SProxy "functionSchema")

_warnings :: forall a b r. Lens { warnings :: a | r} { warnings :: b | r} a b
_warnings = prop (SProxy :: SProxy "warnings")

_argumentSchema :: forall a b r. Lens {argumentSchema :: a | r} {argumentSchema :: b | r} a b
_argumentSchema = prop (SProxy :: SProxy "argumentSchema")

_functionName :: forall a b r. Lens {functionName :: a | r} {functionName :: b | r} a b
_functionName = prop (SProxy :: SProxy "functionName")

_blocks :: forall a b r. Lens { blocks :: a | r} { blocks :: b | r} a b
_blocks = prop (SProxy :: SProxy "blocks")

------------------------------------------------------------

data ValidationError
  = Required String
  | Unsupported String

derive instance eqValidationError :: Eq ValidationError

instance showValidationError :: Show ValidationError where
  show (Required path) = path <> " is required."
  show (Unsupported path) = path <> " is unsupported."

class Validation ctx a where
  validate :: ctx -> a -> Array ValidationError

instance actionValidation :: Validation Unit Action where
  validate _ (Wait _) = []
  validate _ (Action action) =
    Array.concat $ Array.mapWithIndex (validate <<< show) args
    where
      args :: Array SimpleArgument
      args = view (_functionSchema <<< _FunctionSchema <<< _argumentSchema) action

instance simpleArgumentValidation :: Validation String SimpleArgument where
  validate path Unknowable = [ Unsupported path ]
  validate path (SimpleInt Nothing) = [ Required path ]
  validate path (SimpleInt (Just _)) = []
  validate path (SimpleString Nothing) = [ Required path ]
  validate path (SimpleString (Just _)) = []
  validate path (SimpleObject subArguments) =
    Array.concat $
      (\(Tuple name subArgument) -> addPath path <$> validate name subArgument)
      <$>
      subArguments

addPath :: String -> ValidationError -> ValidationError
addPath path (Required subpath) = Required $ path <> "." <> subpath
addPath path (Unsupported subpath) = Unsupported $ path <> "." <> subpath

------------------------------------------------------------

data Query a
  = HandleEditorMessage AceMessage a
  | HandleDragEvent DragEvent a
  | HandleDropEvent DragEvent a
  | HandleMockchainChartMessage EChartsMessage a
  | HandleBalancesChartMessage EChartsMessage a
  | LoadScript String a
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
  = SetIntField (Maybe Int) a
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

type Blockchain = Array (Array Tx)

type State =
  { compilationResult :: RemoteData AjaxError (Either (Array CompilationError) CompilationResult)
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

_compilationResult :: forall s a. Lens' {compilationResult :: a | s} a
_compilationResult = prop (SProxy :: SProxy "compilationResult")

------------------------------------------------------------

data SimpleArgument
  = SimpleInt (Maybe Int)
  | SimpleString (Maybe String)
  | SimpleObject (Array (Tuple String SimpleArgument))
  | Unknowable

derive instance genericSimpleArgument :: Generic SimpleArgument

instance showSimpleArgument :: Show SimpleArgument where
  show = gShow

toValue :: SimpleArgumentSchema -> SimpleArgument
toValue SimpleIntArgument = SimpleInt Nothing
toValue SimpleStringArgument = SimpleString Nothing
toValue (SimpleObjectArgument fields) = SimpleObject (over (traversed <<< _2) toValue fields)
toValue (UnknownArgument _) = Unknowable

-- | This should just be `map` but we can't put an orphan instance on FunctionSchema. :-(
toValueLevel :: FunctionSchema SimpleArgumentSchema -> FunctionSchema SimpleArgument
toValueLevel = over (_Newtype <<< _argumentSchema <<< traversed) toValue
