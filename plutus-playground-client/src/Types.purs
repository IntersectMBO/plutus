module Types where

import Prelude

import Ace.Halogen.Component (AceMessage, AceQuery)
import Auth (AuthStatus)
import Control.Comonad (class Comonad, extract)
import Control.Extend (class Extend, extend)
import Cursor (Cursor)
import DOM.HTML.Event.Types (DragEvent)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Core as Json
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Either (Either)
import Data.Either.Nested (Either3)
import Data.Functor.Coproduct.Nested (Coproduct3)
import Data.Generic (class Generic, gEq, gShow)
import Data.Int as Int
import Data.Lens (Lens, Lens', Prism', _2, over, prism', to, traversed, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Data.NonEmpty ((:|))
import Data.RawJson (RawJson(..))
import Data.StrMap as M
import Data.Symbol (SProxy(..))
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Gist (Gist)
import Halogen.Component.ChildPath (ChildPath, cp1, cp2, cp3)
import Halogen.ECharts (EChartsMessage, EChartsQuery)
import Language.Haskell.Interpreter (SourceCode, InterpreterError, InterpreterResult)
import Ledger.Ada.TH (Ada, _Ada)
import Ledger.Tx (Tx, TxIdOf)
import Matryoshka (class Corecursive, class Recursive, Algebra, cata)
import Network.RemoteData (RemoteData)
import Playground.API (CompilationResult, Evaluation(Evaluation), EvaluationResult, FunctionSchema, SimpleArgumentSchema(UnknownSchema, SimpleObjectSchema, SimpleTupleSchema, SimpleArraySchema, SimpleStringSchema, SimpleIntSchema), SimulatorWallet, _FunctionSchema, _SimulatorWallet)
import Playground.API as API
import Servant.PureScript.Affjax (AjaxError)
import Test.QuickCheck.Arbitrary (class Arbitrary)
import Test.QuickCheck.Gen as Gen
import Validation (class Validation, ValidationError(Unsupported, Required), WithPath, addPath, noPath, validate)
import Wallet.Emulator.Types (Wallet, _Wallet)

_simulatorWalletWallet :: Lens' SimulatorWallet Wallet
_simulatorWalletWallet = _SimulatorWallet <<< prop (SProxy :: SProxy "simulatorWalletWallet")

_simulatorWalletBalance :: Lens' SimulatorWallet Ada
_simulatorWalletBalance = _SimulatorWallet <<< prop (SProxy :: SProxy "simulatorWalletBalance")

_walletId :: Lens' Wallet Int
_walletId = _Wallet <<< prop (SProxy :: SProxy "getWallet")

_ada :: Lens' Ada Int
_ada = _Ada <<< prop (SProxy :: SProxy "getAda")

data Action
  = Action
      { simulatorWallet :: SimulatorWallet
      , functionSchema :: FunctionSchema SimpleArgument
      }
  | Wait { blocks :: Int }

instance eqAction :: Eq Action where
  eq = gEq

derive instance genericAction :: Generic Action

instance showAction :: Show Action where
  show = gShow

_Action ::
  Prism'
    Action
    { simulatorWallet :: SimulatorWallet
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

_argumentSchema :: forall a b r. Lens {argumentSchema :: a | r} {argumentSchema :: b | r} a b
_argumentSchema = prop (SProxy :: SProxy "argumentSchema")

_functionName :: forall a b r. Lens {functionName :: a | r} {functionName :: b | r} a b
_functionName = prop (SProxy :: SProxy "functionName")

_blocks :: forall a b r. Lens { blocks :: a | r} { blocks :: b | r} a b
_blocks = prop (SProxy :: SProxy "blocks")

instance actionValidation :: Validation Action where
  validate (Wait _) = []
  validate (Action action) =
    Array.concat $ Array.mapWithIndex (\i v -> addPath (show i) <$> validate v) args
    where
      args :: Array SimpleArgument
      args = view (_functionSchema <<< _FunctionSchema <<< _argumentSchema) action

------------------------------------------------------------

-- | TODO: It should always be true that either toExpression returns a
-- `Just value` OR validate returns a non-empty array.
-- This suggests they should be the same function, returning either a group of error messages, or a valid expression.
toExpression :: Action -> Maybe API.Expression
toExpression (Wait wait) = Just $ API.Wait wait
toExpression (Action action) = do
  let wallet = view _simulatorWalletWallet action.simulatorWallet
  arguments <- jsonArguments
  pure $ API.Action { wallet, function, arguments }
  where
    function = view (_functionSchema <<< to unwrap <<< _functionName) action
    argumentSchema = view (_functionSchema <<< to unwrap <<< _argumentSchema) action

    jsonArguments = do
      jsonValues <- traverse simpleArgumentToJson argumentSchema
      pure $ RawJson <<< Json.stringify <$> jsonValues

toEvaluation :: SourceCode -> Simulation -> Maybe Evaluation
toEvaluation sourceCode (Simulation {actions, wallets}) = do
    program <- traverse toExpression actions
    pure $ Evaluation { wallets
                      , program
                      , sourceCode
                      , blockchain: []
                      }

------------------------------------------------------------

data Query a
  -- SubEvents.
  = HandleEditorMessage AceMessage a
  | HandleDragEvent DragEvent a
  | HandleDropEvent DragEvent a
  | HandleMockchainChartMessage EChartsMessage a
  | HandleBalancesChartMessage EChartsMessage a
  -- Gist support.
  | CheckAuthStatus a
  | PublishGist a
  | SetGistUrl String a
  | LoadGist a
  -- Tabs.
  | ChangeView View a
  -- Editor.
  | LoadScript String a
  | CompileProgram a
  | ScrollTo { row :: Int, column :: Int } a
  -- Simulations
  | AddSimulationSlot a
  | SetSimulationSlot Int a
  | RemoveSimulationSlot Int a
  -- Wallets.
  | AddWallet a
  | RemoveWallet Int a
  | SetBalance Wallet Ada a
  -- Actions.
  | ModifyActions ActionEvent a
  | EvaluateActions a
  | PopulateAction Int Int (FormEvent a)

data ActionEvent
  = AddAction Action
  | AddWaitAction Int
  | RemoveAction Int
  | SetWaitTime Int Int

data FormEvent a
  = SetIntField (Maybe Int) a
  | SetStringField String a
  | AddSubField a
  | SetSubField Int (FormEvent a)
  | RemoveSubField Int a

derive instance functorFormEvent :: Functor FormEvent

instance extendFormEvent :: Extend FormEvent where
  extend f event@(SetIntField n _) = SetIntField n $ f event
  extend f event@(SetStringField s _) = SetStringField s $ f event
  extend f event@(AddSubField _) = AddSubField $ f event
  extend f event@(SetSubField n _) = SetSubField n $ extend f event
  extend f event@(RemoveSubField n _) = RemoveSubField n $ f event

instance comonadFormEvent :: Comonad FormEvent where
  extract (SetIntField _ a) = a
  extract (SetStringField _ a) = a
  extract (AddSubField a) = a
  extract (SetSubField _ e) = extract e
  extract (RemoveSubField _ e) = e

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

type Blockchain = Array (Array (Tuple (TxIdOf String) Tx))
type Signatures = Array (FunctionSchema SimpleArgumentSchema)
newtype Simulation = Simulation
  { signatures :: Signatures
  , actions :: Array Action
  , wallets :: Array SimulatorWallet
  }

derive instance newtypeSimulation :: Newtype Simulation _
derive instance genericSimulation :: Generic Simulation

type WebData = RemoteData AjaxError

newtype State = State
  { currentView :: View
  , compilationResult :: WebData (Either InterpreterError (InterpreterResult CompilationResult))
  , simulations :: Cursor Simulation
  , evaluationResult :: WebData EvaluationResult
  , authStatus :: WebData AuthStatus
  , createGistResult :: WebData Gist
  , gistUrl :: Maybe String
  }

derive instance newtypeState :: Newtype State _

_currentView :: Lens' State View
_currentView = _Newtype <<< prop (SProxy :: SProxy "currentView")

_simulations :: Lens' State (Cursor Simulation)
_simulations = _Newtype <<< prop (SProxy :: SProxy "simulations")

_signatures :: Lens' Simulation Signatures
_signatures = _Newtype <<< prop (SProxy :: SProxy "signatures")

_actions :: Lens' Simulation (Array Action)
_actions = _Newtype <<< prop (SProxy :: SProxy "actions")

_wallets :: Lens' Simulation (Array SimulatorWallet)
_wallets = _Newtype <<< prop (SProxy :: SProxy "wallets")

_evaluationResult :: Lens' State (WebData EvaluationResult)
_evaluationResult = _Newtype <<< prop (SProxy :: SProxy "evaluationResult")

_compilationResult :: Lens' State (WebData (Either InterpreterError (InterpreterResult CompilationResult)))
_compilationResult = _Newtype <<< prop (SProxy :: SProxy "compilationResult")

_authStatus :: Lens' State (WebData AuthStatus)
_authStatus = _Newtype <<< prop (SProxy :: SProxy "authStatus")

_createGistResult :: Lens' State (WebData Gist)
_createGistResult = _Newtype <<< prop (SProxy :: SProxy "createGistResult")

_gistUrl :: Lens' State (Maybe String)
_gistUrl = _Newtype <<< prop (SProxy :: SProxy "gistUrl")

_resultBlockchain :: Lens' EvaluationResult Blockchain
_resultBlockchain = _Newtype <<< prop (SProxy :: SProxy "resultBlockchain")

data View
  = Editor
  | Simulations
  | Transactions

derive instance eqView :: Eq View
derive instance genericView :: Generic View

instance arbitraryView :: Arbitrary View where
  arbitrary = Gen.elements (Editor :| [ Simulations, Transactions ])

instance showView :: Show View where
  show Editor = "Editor"
  show Simulations = "Simulation"
  show Transactions = "Transactions"

------------------------------------------------------------

data SimpleArgument
  = SimpleInt (Maybe Int)
  | SimpleString (Maybe String)
  | SimpleArray SimpleArgumentSchema (Array SimpleArgument)
  | SimpleTuple (Tuple SimpleArgument SimpleArgument)
  | SimpleObject SimpleArgumentSchema (Array (Tuple String SimpleArgument))
  | Unknowable { context :: String, description :: String }

derive instance genericSimpleArgument :: Generic SimpleArgument

instance showSimpleArgument :: Show SimpleArgument where
  show = gShow

toValue :: SimpleArgumentSchema -> SimpleArgument
toValue SimpleIntSchema = SimpleInt Nothing
toValue SimpleStringSchema = SimpleString Nothing
toValue (SimpleArraySchema field) = SimpleArray field []
toValue (SimpleTupleSchema (fieldA /\ fieldB)) = SimpleTuple (toValue fieldA /\ toValue fieldB)
toValue schema@(SimpleObjectSchema fields) = SimpleObject schema (over (traversed <<< _2) toValue fields)
toValue (UnknownSchema context description) = Unknowable { context, description }

-- | This should just be `map` but we can't put an orphan instance on FunctionSchema. :-(
toValueLevel :: FunctionSchema SimpleArgumentSchema -> FunctionSchema SimpleArgument
toValueLevel = over (_Newtype <<< _argumentSchema <<< traversed) toValue

------------------------------------------------------------

-- | This type serves as a functorised version of `SimpleArgument` so
-- we can do some recursive processing of the data without cluttering
-- the transformation with the iteration.
data SimpleArgumentF a
  = SimpleIntF (Maybe Int)
  | SimpleStringF (Maybe String)
  | SimpleTupleF (Tuple a a)
  | SimpleArrayF SimpleArgumentSchema (Array a)
  | SimpleObjectF SimpleArgumentSchema (Array (Tuple String a))
  | UnknowableF { context :: String, description :: String }

instance functorSimpleArgumentF :: Functor SimpleArgumentF where
  map f (SimpleIntF x) = SimpleIntF x
  map f (SimpleStringF x) = SimpleStringF x
  map f (SimpleTupleF (Tuple x y)) = SimpleTupleF (Tuple (f x) (f y))
  map f (SimpleArrayF schema xs) = SimpleArrayF schema (map f xs)
  map f (SimpleObjectF schema xs) = SimpleObjectF schema (map (map f) xs)
  map f (UnknowableF x) = UnknowableF x

derive instance eqSimpleArgumentF :: Eq a => Eq (SimpleArgumentF a)

instance recursiveSimpleArgument :: Recursive SimpleArgument SimpleArgumentF where
  project (SimpleInt x) = SimpleIntF x
  project (SimpleString x) = SimpleStringF x
  project (SimpleTuple x) = SimpleTupleF x
  project (SimpleArray schema xs) = SimpleArrayF schema xs
  project (SimpleObject schema xs) = SimpleObjectF schema xs
  project (Unknowable x) = UnknowableF x

instance corecursiveSimpleArgument :: Corecursive SimpleArgument SimpleArgumentF where
  embed (SimpleIntF x) = SimpleInt x
  embed (SimpleStringF x) = SimpleString x
  embed (SimpleTupleF xs) = SimpleTuple xs
  embed (SimpleArrayF schema xs) = SimpleArray schema xs
  embed (SimpleObjectF schema xs) = SimpleObject schema xs
  embed (UnknowableF x) = Unknowable x

------------------------------------------------------------

instance validationSimpleArgument :: Validation SimpleArgument where
  validate = cata algebra
    where
      algebra :: Algebra SimpleArgumentF (Array (WithPath ValidationError))
      algebra (SimpleIntF (Just _)) = []
      algebra (SimpleIntF Nothing) = [ noPath Required ]

      algebra (SimpleStringF (Just _)) = []
      algebra (SimpleStringF Nothing) = [ noPath Required ]

      algebra (SimpleTupleF (Tuple xs ys)) =
        Array.concat [ addPath "_1" <$> xs
                     , addPath "_2" <$> ys
                     ]

      algebra (SimpleArrayF schema xs) =
        Array.concat $ mapWithIndex (\i values-> addPath (show i) <$> values) xs

      algebra (SimpleObjectF schema xs) =
        Array.concat $ map (\(Tuple name values) -> addPath name <$> values) xs

      algebra (UnknowableF _) = [ noPath Unsupported ]

simpleArgumentToJson :: SimpleArgument -> Maybe Json
simpleArgumentToJson = cata algebra
  where
    algebra :: Algebra SimpleArgumentF (Maybe Json)
    algebra (SimpleIntF (Just str)) = Just $ Json.fromNumber $ Int.toNumber str
    algebra (SimpleIntF Nothing) = Nothing
    algebra (SimpleStringF (Just str)) = Just $ Json.fromString str
    algebra (SimpleStringF Nothing) = Nothing
    algebra (SimpleTupleF (Just fieldA /\ Just fieldB)) = Just $ Json.fromArray [ fieldA, fieldB ]
    algebra (SimpleTupleF _) = Nothing
    algebra (SimpleArrayF _ fields) = Json.fromArray <$> sequence fields
    algebra (SimpleObjectF _ fields) = (Json.fromObject <<< M.fromFoldable) <$> sequence (map sequence fields)
    algebra (UnknowableF _) = Nothing

--- Language.Haskell.Interpreter ---

_result :: forall s a. Lens' {result :: a | s} a
_result = prop (SProxy :: SProxy "result")

_warnings :: forall s a. Lens' {warnings :: a | s} a
_warnings = prop (SProxy :: SProxy "warnings")
