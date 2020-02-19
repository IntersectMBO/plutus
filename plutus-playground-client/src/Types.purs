module Types where

import Prelude
import Ace.Halogen.Component (AceMessage, AceQuery)
import Auth (AuthStatus)
import Chain.Types (ChainFocus)
import Chain.Types as Chain
import Control.Monad.State.Class (class MonadState)
import Cursor (Cursor)
import Data.Array as Array
import Data.Foldable (fold, foldMap)
import Data.Functor.Foldable (Fix)
import Data.Generic.Rep (class Generic)
import Data.Json.JsonEither (JsonEither)
import Data.Json.JsonTuple (JsonTuple)
import Data.Lens (Iso', Lens', Traversal', _Right, iso)
import Data.Lens.Extra (peruse)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.NonEmpty ((:|))
import Data.RawJson (RawJson(..))
import Data.String.Extra (toHex) as String
import Data.Symbol (SProxy(..))
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Editor as Editor
import Foreign (Foreign)
import Foreign.Class (encode)
import Foreign.Generic (encodeJSON)
import Foreign.Object as FO
import Gist (Gist)
import Gists (GistAction)
import Halogen as H
import Halogen.Chartist as Chartist
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode, _InterpreterResult)
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Crypto (PubKey, PubKeyHash, _PubKey)
import Ledger.Interval (Extended(..), Interval(..), LowerBound(..), UpperBound(..))
import Ledger.Slot (Slot)
import Ledger.Tx (Tx)
import Ledger.Value (CurrencySymbol(..), TokenName, Value(..), _CurrencySymbol, _TokenName, _Value)
import Matryoshka (Algebra, ana, cata)
import Network.RemoteData (RemoteData, _Success)
import Playground.Types (CompilationResult, ContractCall(..), ContractDemo, Evaluation(..), EvaluationResult, FunctionSchema(..), KnownCurrency(..), PlaygroundError, Simulation(..), SimulatorWallet, _SimulatorWallet)
import Schema (FormSchema(..), FormArgumentF(..))
import Servant.PureScript.Ajax (AjaxError)
import Test.QuickCheck.Arbitrary (class Arbitrary)
import Test.QuickCheck.Gen as Gen
import Wallet.Emulator.Wallet (Wallet, _Wallet)
import Wallet.Rollup.Types (AnnotatedTx)
import Web.HTML.Event.DragEvent (DragEvent)

type FormArgument
  = Fix FormArgumentF

type SimulatorAction
  = ContractCall FormArgument

type Expression
  = ContractCall RawJson

_simulatorWallet :: forall r a. Lens' { simulatorWallet :: a | r } a
_simulatorWallet = prop (SProxy :: SProxy "simulatorWallet")

_simulatorWalletWallet :: Lens' SimulatorWallet Wallet
_simulatorWalletWallet = _SimulatorWallet <<< prop (SProxy :: SProxy "simulatorWalletWallet")

_simulatorWalletBalance :: Lens' SimulatorWallet Value
_simulatorWalletBalance = _SimulatorWallet <<< prop (SProxy :: SProxy "simulatorWalletBalance")

_walletId :: Iso' Wallet Int
_walletId = _Wallet <<< iso _.getWallet { getWallet: _ }

_pubKey :: Lens' PubKey String
_pubKey = _PubKey <<< prop (SProxy :: SProxy "getPubKey")

_value :: Lens' Value (AssocMap.Map CurrencySymbol (AssocMap.Map TokenName Int))
_value = _Value <<< prop (SProxy :: SProxy "getValue")

_waitBlocks :: forall r a. Lens' { waitBlocks :: a | r } a
_waitBlocks = prop (SProxy :: SProxy "waitBlocks")

_functionSchema :: Lens' CompilationResult (Array (FunctionSchema FormSchema))
_functionSchema = _Newtype <<< prop (SProxy :: SProxy "functionSchema")

_caller :: forall r a. Lens' { caller :: a | r } a
_caller = prop (SProxy :: SProxy "caller")

_functionArguments :: forall r a. Lens' { functionArguments :: a | r } a
_functionArguments = prop (SProxy :: SProxy "functionArguments")

_amount :: forall r a. Lens' { amount :: a | r } a
_amount = prop (SProxy :: SProxy "amount")

_recipient :: forall r a. Lens' { recipient :: a | r } a
_recipient = prop (SProxy :: SProxy "recipient")

_blocks :: forall r a. Lens' { blocks :: a | r } a
_blocks = prop (SProxy :: SProxy "blocks")

_InSlot :: Iso' Slot Int
_InSlot = iso (_.getSlot <<< unwrap) (wrap <<< { getSlot: _ })

_slot :: forall r a. Lens' { slot :: a | r } a
_slot = prop (SProxy :: SProxy "slot")

_endpointName :: forall r a. Lens' { endpointName :: a | r } a
_endpointName = prop (SProxy :: SProxy "endpointName")

_functionName :: forall r a. Lens' { functionName :: a | r } a
_functionName = prop (SProxy :: SProxy "functionName")

_arguments :: forall r a. Lens' { arguments :: a | r } a
_arguments = prop (SProxy :: SProxy "arguments")

_argumentValues :: forall r a. Lens' { argumentValues :: a | r } a
_argumentValues = prop (SProxy :: SProxy "argumentValues")

_argumentSchema :: forall r a. Lens' { argumentSchema :: a | r } a
_argumentSchema = prop (SProxy :: SProxy "argumentSchema")

_currencySymbol :: Lens' CurrencySymbol String
_currencySymbol = _CurrencySymbol <<< prop (SProxy :: SProxy "unCurrencySymbol")

_tokenName :: Lens' TokenName String
_tokenName = _TokenName <<< prop (SProxy :: SProxy "unTokenName")

------------------------------------------------------------
-- | These only exist because of the orphan instance restriction.
traverseFunctionSchema ::
  forall m a b.
  Applicative m =>
  (a -> m b) ->
  FunctionSchema a -> m (FunctionSchema b)
traverseFunctionSchema f (FunctionSchema { endpointName, arguments: oldArguments }) = rewrap <$> traverse f oldArguments
  where
  rewrap newArguments = FunctionSchema { endpointName, arguments: newArguments }

traverseSimulatorAction ::
  forall m b a.
  Applicative m =>
  (a -> m b) ->
  ContractCall a -> m (ContractCall b)
traverseSimulatorAction _ (AddBlocks addBlocks) = pure $ AddBlocks addBlocks

traverseSimulatorAction _ (AddBlocksUntil addBlocksUntil) = pure $ AddBlocksUntil addBlocksUntil

traverseSimulatorAction _ (PayToWallet payToWallet) = pure $ PayToWallet payToWallet

traverseSimulatorAction f (CallEndpoint { caller, argumentValues: oldArgumentValues }) = rewrap <$> traverseFunctionSchema f oldArgumentValues
  where
  rewrap newArgumentValues = CallEndpoint { caller, argumentValues: newArgumentValues }

toExpression :: SimulatorAction -> Maybe Expression
toExpression = traverseSimulatorAction encodeForm
  where
  encodeForm :: FormArgument -> Maybe RawJson
  encodeForm argument = (RawJson <<< encodeJSON) <$> formArgumentToJson argument

toEvaluation :: SourceCode -> Simulation -> Maybe Evaluation
toEvaluation sourceCode (Simulation { simulationActions, simulationWallets }) = do
  program <- RawJson <<< encodeJSON <$> traverse toExpression simulationActions
  pure
    $ Evaluation
        { wallets: simulationWallets
        , program
        , sourceCode
        }

------------------------------------------------------------
data Query a

data HAction
  = Mounted
  -- SubEvents.
  | ActionDragAndDrop Int DragAndDropEventType DragEvent
  | HandleBalancesChartMessage Chartist.Message
  -- Gist support.
  | CheckAuthStatus
  | GistAction GistAction
  -- Tabs.
  | ChangeView View
  -- Editor.
  | EditorAction Editor.Action
  | CompileProgram
  -- Simulations
  | LoadScript String
  | AddSimulationSlot
  | SetSimulationSlot Int
  | RemoveSimulationSlot Int
  -- Wallets.
  | ModifyWallets WalletEvent
  -- Actions.
  | ModifyActions ActionEvent
  | EvaluateActions
  | PopulateAction Int Int FormEvent
  -- Chain.
  | SetChainFocus (Maybe ChainFocus)

data WalletEvent
  = AddWallet
  | RemoveWallet Int
  | ModifyBalance Int ValueEvent

data ValueEvent
  = SetBalance CurrencySymbol TokenName Int

data ActionEvent
  = AddAction SimulatorAction
  | AddWaitAction Int
  | RemoveAction Int
  | SetWaitTime Int Int
  | SetWaitUntilTime Int Slot
  | SetPayToWalletValue Int ValueEvent
  | SetPayToWalletRecipient Int Wallet

data DragAndDropEventType
  = DragStart
  | DragEnd
  | DragEnter
  | DragOver
  | DragLeave
  | Drop

instance showDragAndDropEventType :: Show DragAndDropEventType where
  show DragStart = "DragStart"
  show DragEnd = "DragEnd"
  show DragEnter = "DragEnter"
  show DragOver = "DragOver"
  show DragLeave = "DragLeave"
  show Drop = "Drop"

data FieldEvent
  = SetIntField (Maybe Int)
  | SetBoolField Boolean
  | SetStringField String
  | SetHexField String
  | SetRadioField String
  | SetValueField ValueEvent
  | SetSlotRangeField (Interval Slot)

data FormEvent
  = SetField FieldEvent
  | SetSubField Int FormEvent
  | AddSubField
  | RemoveSubField Int

------------------------------------------------------------
type ChildSlots
  = ( editorSlot :: H.Slot AceQuery AceMessage Unit
    , balancesChartSlot :: H.Slot Chartist.Query Chartist.Message Unit
    )

_editorSlot :: SProxy "editorSlot"
_editorSlot = SProxy

_balancesChartSlot :: SProxy "balancesChartSlot"
_balancesChartSlot = SProxy

-----------------------------------------------------------
type ChainSlot
  = Array Tx

type Blockchain
  = Array ChainSlot

type WebData
  = RemoteData AjaxError

newtype State
  = State
  { currentView :: View
  , contractDemos :: Array ContractDemo
  , editorPreferences :: Editor.Preferences
  , compilationResult :: WebData (JsonEither InterpreterError (InterpreterResult CompilationResult))
  , simulations :: Cursor Simulation
  , actionDrag :: Maybe Int
  , evaluationResult :: WebData (JsonEither PlaygroundError EvaluationResult)
  , authStatus :: WebData AuthStatus
  , createGistResult :: WebData Gist
  , gistUrl :: Maybe String
  , blockchainVisualisationState :: Chain.State
  }

derive instance newtypeState :: Newtype State _

_currentView :: Lens' State View
_currentView = _Newtype <<< prop (SProxy :: SProxy "currentView")

_contractDemos :: Lens' State (Array ContractDemo)
_contractDemos = _Newtype <<< prop (SProxy :: SProxy "contractDemos")

_editorPreferences :: Lens' State Editor.Preferences
_editorPreferences = _Newtype <<< prop (SProxy :: SProxy "editorPreferences")

_simulations :: Lens' State (Cursor Simulation)
_simulations = _Newtype <<< prop (SProxy :: SProxy "simulations")

_actionDrag :: Lens' State (Maybe Int)
_actionDrag = _Newtype <<< prop (SProxy :: SProxy "actionDrag")

type Signatures
  = Array (FunctionSchema FormSchema)

_simulationActions :: Lens' Simulation (Array SimulatorAction)
_simulationActions = _Newtype <<< prop (SProxy :: SProxy "simulationActions")

_simulationWallets :: Lens' Simulation (Array SimulatorWallet)
_simulationWallets = _Newtype <<< prop (SProxy :: SProxy "simulationWallets")

_evaluationResult :: Lens' State (WebData (JsonEither PlaygroundError EvaluationResult))
_evaluationResult = _Newtype <<< prop (SProxy :: SProxy "evaluationResult")

_resultRollup :: Lens' EvaluationResult (Array (Array AnnotatedTx))
_resultRollup = _Newtype <<< prop (SProxy :: SProxy "resultRollup")

_compilationResult :: Lens' State (WebData (JsonEither InterpreterError (InterpreterResult CompilationResult)))
_compilationResult = _Newtype <<< prop (SProxy :: SProxy "compilationResult")

_successfulCompilationResult :: Traversal' State CompilationResult
_successfulCompilationResult = _compilationResult <<< _Success <<< _Newtype <<< _Right <<< _InterpreterResult <<< _result

_authStatus :: Lens' State (WebData AuthStatus)
_authStatus = _Newtype <<< prop (SProxy :: SProxy "authStatus")

_createGistResult :: Lens' State (WebData Gist)
_createGistResult = _Newtype <<< prop (SProxy :: SProxy "createGistResult")

_gistUrl :: Lens' State (Maybe String)
_gistUrl = _Newtype <<< prop (SProxy :: SProxy "gistUrl")

_resultBlockchain :: Lens' EvaluationResult Blockchain
_resultBlockchain = _Newtype <<< prop (SProxy :: SProxy "resultBlockchain")

_walletKeys :: Lens' EvaluationResult (Array (JsonTuple PubKeyHash Wallet))
_walletKeys = _Newtype <<< prop (SProxy :: SProxy "walletKeys")

_knownCurrencies :: Lens' CompilationResult (Array KnownCurrency)
_knownCurrencies = _Newtype <<< prop (SProxy :: SProxy "knownCurrencies")

_blockchainVisualisationState :: Lens' State Chain.State
_blockchainVisualisationState = _Newtype <<< prop (SProxy :: SProxy "blockchainVisualisationState")

_x :: forall r a. Lens' { x :: a | r } a
_x = prop (SProxy :: SProxy "x")

_y :: forall r a. Lens' { y :: a | r } a
_y = prop (SProxy :: SProxy "y")

data View
  = Editor
  | Simulations
  | Transactions

derive instance eqView :: Eq View

derive instance genericView :: Generic View _

instance arbitraryView :: Arbitrary View where
  arbitrary = Gen.elements (Editor :| [ Simulations, Transactions ])

instance showView :: Show View where
  show Editor = "Editor"
  show Simulations = "Simulation"
  show Transactions = "Transactions"

------------------------------------------------------------
toArgument :: Value -> FormSchema -> FormArgument
toArgument initialValue = ana algebra
  where
  algebra :: FormSchema -> FormArgumentF FormSchema
  algebra FormSchemaUnit = FormUnitF

  algebra FormSchemaBool = FormBoolF false

  algebra FormSchemaInt = FormIntF Nothing

  algebra FormSchemaString = FormStringF Nothing

  algebra FormSchemaHex = FormHexF Nothing

  algebra (FormSchemaRadio xs) = FormRadioF xs Nothing

  algebra (FormSchemaArray xs) = FormArrayF xs []

  algebra (FormSchemaMaybe x) = FormMaybeF x Nothing

  algebra FormSchemaValue = FormValueF initialValue

  algebra FormSchemaSlotRange = FormSlotRangeF defaultSlotRange

  algebra (FormSchemaTuple a b) = FormTupleF a b

  algebra (FormSchemaObject xs) = FormObjectF xs

  algebra (FormSchemaUnsupported x) = FormUnsupportedF x

defaultSlotRange :: Interval Slot
defaultSlotRange =
  Interval
    { ivFrom: LowerBound NegInf true
    , ivTo: UpperBound PosInf true
    }

------------------------------------------------------------
formArgumentToJson :: FormArgument -> Maybe Foreign
formArgumentToJson = cata algebra
  where
  algebra :: Algebra FormArgumentF (Maybe Foreign)
  algebra FormUnitF = Just $ encode (mempty :: Array Unit)

  algebra (FormBoolF b) = Just $ encode b

  algebra (FormIntF n) = encode <$> n

  algebra (FormStringF str) = encode <$> str

  algebra (FormRadioF _ option) = encode <$> option

  algebra (FormHexF str) = encode <<< String.toHex <$> str

  algebra (FormTupleF (Just fieldA) (Just fieldB)) = Just $ encode [ fieldA, fieldB ]

  algebra (FormTupleF _ _) = Nothing

  algebra (FormMaybeF _ field) = encode <$> field

  algebra (FormArrayF _ fields) = Just $ encode fields

  algebra (FormObjectF fields) = encodeFields fields
    where
    encodeFields :: Array (JsonTuple String (Maybe Foreign)) -> Maybe Foreign
    encodeFields xs = map (encode <<< FO.fromFoldable) $ prepareObject xs

    prepareObject :: Array (JsonTuple String (Maybe Foreign)) -> Maybe (Array (Tuple String Foreign))
    prepareObject = traverse processTuples

    processTuples :: JsonTuple String (Maybe Foreign) -> Maybe (Tuple String Foreign)
    processTuples = unwrap >>> sequence

  algebra (FormValueF x) = Just $ encode x

  algebra (FormSlotRangeF x) = Just $ encode x

  algebra (FormUnsupportedF _) = Nothing

--- Language.Haskell.Interpreter ---
_result :: forall s a. Lens' { result :: a | s } a
_result = prop (SProxy :: SProxy "result")

_warnings :: forall s a. Lens' { warnings :: a | s } a
_warnings = prop (SProxy :: SProxy "warnings")

getKnownCurrencies :: forall m. MonadState State m => m (Array KnownCurrency)
getKnownCurrencies = fromMaybe [] <$> peruse (_successfulCompilationResult <<< _knownCurrencies)

mkInitialValue :: Array KnownCurrency -> Int -> Value
mkInitialValue currencies initialBalance = Value { getValue: value }
  where
  value =
    map (map unwrap)
      $ fold
      $ foldMap
          ( \(KnownCurrency { hash, knownTokens }) ->
              map
                ( \tokenName ->
                    AssocMap.fromTuples
                      [ CurrencySymbol { unCurrencySymbol: hash }
                          /\ AssocMap.fromTuples [ tokenName /\ Additive initialBalance ]
                      ]
                )
                $ Array.fromFoldable knownTokens
          )
          currencies
