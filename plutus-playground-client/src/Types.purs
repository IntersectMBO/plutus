module Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Auth (AuthStatus)
import Chain.Types (Action(..))
import Chain.Types as Chain
import Clipboard as Clipboard
import Control.Monad.State.Class (class MonadState)
import Cursor (Cursor)
import Data.BigInteger (BigInteger)
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Json.JsonTuple (JsonTuple)
import Data.Lens (Iso', Lens', Traversal', _Right, iso)
import Data.Lens.Extra (peruse)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.NonEmpty ((:|))
import Data.RawJson (RawJson(..))
import Data.Symbol (SProxy(..))
import Data.Traversable (traverse)
import Editor.Types as Editor
import Foreign.Generic (encodeJSON)
import Gist (Gist)
import Gists.Types (GistAction(..))
import Halogen as H
import Halogen.Chartist as Chartist
import Halogen.Monaco as Monaco
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode, _InterpreterResult)
import Ledger.Crypto (PubKey, PubKeyHash, _PubKey)
import Ledger.Slot (Slot)
import Ledger.Tx (Tx)
import Ledger.Value (Value)
import Network.RemoteData (RemoteData, _Success)
import Playground.Types (CompilationResult, ContractCall(..), ContractDemo, Evaluation(..), EvaluationResult, FunctionSchema, KnownCurrency, PlaygroundError, Simulation(..), SimulatorWallet, _SimulatorWallet)
import Schema (FormSchema)
import Schema.Types (ActionEvent(..), Expression, FormArgument, SimulationAction(..), formArgumentToJson, traverseFunctionSchema)
import Servant.PureScript.Ajax (AjaxError)
import Test.QuickCheck.Arbitrary (class Arbitrary)
import Test.QuickCheck.Gen as Gen
import ValueEditor (ValueEvent(..))
import Wallet.Emulator.Wallet (Wallet, _Wallet)
import Wallet.Rollup.Types (AnnotatedTx)
import Web.HTML.Event.DragEvent (DragEvent)

_simulatorWallet :: forall r a. Lens' { simulatorWallet :: a | r } a
_simulatorWallet = prop (SProxy :: SProxy "simulatorWallet")

_simulatorWalletWallet :: Lens' SimulatorWallet Wallet
_simulatorWalletWallet = _SimulatorWallet <<< prop (SProxy :: SProxy "simulatorWalletWallet")

_simulatorWalletBalance :: Lens' SimulatorWallet Value
_simulatorWalletBalance = _SimulatorWallet <<< prop (SProxy :: SProxy "simulatorWalletBalance")

_walletId :: Iso' Wallet BigInteger
_walletId = _Wallet <<< iso _.getWallet { getWallet: _ }

_pubKey :: Lens' PubKey String
_pubKey = _PubKey <<< prop (SProxy :: SProxy "getPubKey")

_waitBlocks :: forall r a. Lens' { waitBlocks :: a | r } a
_waitBlocks = prop (SProxy :: SProxy "waitBlocks")

_functionSchema :: Lens' CompilationResult (Array (FunctionSchema FormSchema))
_functionSchema = _Newtype <<< prop (SProxy :: SProxy "functionSchema")

_caller :: forall r a. Lens' { caller :: a | r } a
_caller = prop (SProxy :: SProxy "caller")

_functionArguments :: forall r a. Lens' { functionArguments :: a | r } a
_functionArguments = prop (SProxy :: SProxy "functionArguments")

_blocks :: forall r a. Lens' { blocks :: a | r } a
_blocks = prop (SProxy :: SProxy "blocks")

_InSlot :: Iso' Slot BigInteger
_InSlot = iso (_.getSlot <<< unwrap) (wrap <<< { getSlot: _ })

_slot :: forall r a. Lens' { slot :: a | r } a
_slot = prop (SProxy :: SProxy "slot")

_functionName :: forall r a. Lens' { functionName :: a | r } a
_functionName = prop (SProxy :: SProxy "functionName")

_argumentSchema :: forall r a. Lens' { argumentSchema :: a | r } a
_argumentSchema = prop (SProxy :: SProxy "argumentSchema")

------------------------------------------------------------
traverseContractCall ::
  forall m b a.
  Applicative m =>
  (a -> m b) ->
  ContractCall a -> m (ContractCall b)
traverseContractCall _ (AddBlocks addBlocks) = pure $ AddBlocks addBlocks

traverseContractCall _ (AddBlocksUntil addBlocksUntil) = pure $ AddBlocksUntil addBlocksUntil

traverseContractCall _ (PayToWallet payToWallet) = pure $ PayToWallet payToWallet

traverseContractCall f (CallEndpoint { caller, argumentValues: oldArgumentValues }) = rewrap <$> traverseFunctionSchema f oldArgumentValues
  where
  rewrap newArgumentValues = CallEndpoint { caller, argumentValues: newArgumentValues }

toExpression :: ContractCall FormArgument -> Maybe Expression
toExpression = traverseContractCall encodeForm
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
  = Init
  | Mounted
  -- SubEvents.
  | ActionDragAndDrop Int DragAndDropEventType DragEvent
  | HandleBalancesChartMessage Chartist.Message
  -- Gist support.
  | CheckAuthStatus
  | GistAction GistAction
  -- Demo files menu.
  | ToggleDemoFilesMenu
  -- Tabs.
  | ChangeView View
  -- Editor.
  | EditorAction Editor.Action
  | CompileProgram
  -- Simulations.
  | LoadScript String
  | AddSimulationSlot
  | SetSimulationSlot Int
  | RemoveSimulationSlot Int
  -- Wallets.
  | ModifyWallets WalletEvent
  -- Actions.
  | ChangeSimulation SimulationAction
  | EvaluateActions
  -- Chain.
  | ChainAction (Chain.Action)

data WalletEvent
  = AddWallet
  | RemoveWallet Int
  | ModifyBalance Int ValueEvent

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

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent HAction where
  toEvent Init = Nothing
  toEvent Mounted = Just $ defaultEvent "Mounted"
  toEvent (EditorAction (Editor.HandleDropEvent _)) = Just $ defaultEvent "DropScript"
  toEvent (EditorAction action) = Just $ (defaultEvent "ConfigureEditor")
  toEvent CompileProgram = Just $ defaultEvent "CompileProgram"
  toEvent (HandleBalancesChartMessage _) = Nothing
  toEvent CheckAuthStatus = Nothing
  toEvent (GistAction PublishGist) = Just $ (defaultEvent "Publish") { category = Just "Gist" }
  toEvent (GistAction (SetGistUrl _)) = Nothing
  toEvent (GistAction LoadGist) = Just $ (defaultEvent "LoadGist") { category = Just "Gist" }
  toEvent (GistAction (AjaxErrorPaneAction _)) = Nothing
  toEvent ToggleDemoFilesMenu = Nothing
  toEvent (ChangeView view) = Just $ (defaultEvent "View") { label = Just $ show view }
  toEvent (LoadScript script) = Just $ (defaultEvent "LoadScript") { label = Just script }
  toEvent AddSimulationSlot = Just $ (defaultEvent "AddSimulationSlot") { category = Just "Simulation" }
  toEvent (SetSimulationSlot _) = Just $ (defaultEvent "SetSimulationSlot") { category = Just "Simulation" }
  toEvent (RemoveSimulationSlot _) = Just $ (defaultEvent "RemoveSimulationSlot") { category = Just "Simulation" }
  toEvent (ModifyWallets AddWallet) = Just $ (defaultEvent "AddWallet") { category = Just "Wallet" }
  toEvent (ModifyWallets (RemoveWallet _)) = Just $ (defaultEvent "RemoveWallet") { category = Just "Wallet" }
  toEvent (ModifyWallets (ModifyBalance _ (SetBalance _ _ _))) = Just $ (defaultEvent "SetBalance") { category = Just "Wallet" }
  toEvent (ActionDragAndDrop _ eventType _) = Just $ (defaultEvent (show eventType)) { category = Just "Action" }
  toEvent EvaluateActions = Just $ (defaultEvent "EvaluateActions") { category = Just "Action" }
  toEvent (ChangeSimulation (PopulateAction _ _)) = Just $ (defaultEvent "PopulateAction") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (AddAction _))) = Just $ (defaultEvent "AddAction") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (AddWaitAction _))) = Just $ (defaultEvent "AddWaitAction") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (RemoveAction _))) = Just $ (defaultEvent "RemoveAction") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (SetPayToWalletValue _ _))) = Just $ (defaultEvent "SetPayToWalletValue") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (SetPayToWalletRecipient _ _))) = Just $ (defaultEvent "SetPayToWalletRecipient") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (SetWaitTime _ _))) = Just $ (defaultEvent "SetWaitTime") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (SetWaitUntilTime _ _))) = Just $ (defaultEvent "SetWaitUntilTime") { category = Just "Action" }
  toEvent (ChainAction (FocusTx (Just _))) = Just $ (defaultEvent "BlockchainFocus") { category = Just "Transaction" }
  toEvent (ChainAction (FocusTx Nothing)) = Nothing
  toEvent (ChainAction (ClipboardAction (Clipboard.CopyToClipboard _))) = Just $ (defaultEvent "ClipboardAction") { category = Just "CopyToClipboard" }

------------------------------------------------------------
type ChildSlots
  = ( editorSlot :: H.Slot Monaco.Query Monaco.Message Unit
    , balancesChartSlot :: H.Slot Chartist.Query Chartist.Message Unit
    )

_editorSlot :: SProxy "editorSlot"
_editorSlot = SProxy

_balancesChartSlot :: SProxy "balancesChartSlot"
_balancesChartSlot = SProxy

------------------------------------------------------------
type ChainSlot
  = Array Tx

type Blockchain
  = Array ChainSlot

type WebData
  = RemoteData AjaxError

type WebCompilationResult
  = WebData (Either InterpreterError (InterpreterResult CompilationResult))

type WebEvaluationResult
  = WebData (Either PlaygroundError EvaluationResult)

-- this synonym is defined in playground-common/src/Playground/Types.hs
type SimulatorAction
  = ContractCall FormArgument

newtype State
  = State
  { demoFilesMenuVisible :: Boolean
  , gistErrorPaneVisible :: Boolean
  , currentView :: View
  , contractDemos :: Array ContractDemo
  , currentDemoName :: Maybe String
  , editorState :: Editor.State
  , compilationResult :: WebCompilationResult
  , simulations :: Cursor Simulation
  , actionDrag :: Maybe Int
  , evaluationResult :: WebEvaluationResult
  , lastEvaluatedSimulation :: Maybe Simulation
  , authStatus :: WebData AuthStatus
  , createGistResult :: WebData Gist
  , gistUrl :: Maybe String
  , blockchainVisualisationState :: Chain.State
  }

derive instance newtypeState :: Newtype State _

_demoFilesMenuVisible :: Lens' State Boolean
_demoFilesMenuVisible = _Newtype <<< prop (SProxy :: SProxy "demoFilesMenuVisible")

_gistErrorPaneVisible :: Lens' State Boolean
_gistErrorPaneVisible = _Newtype <<< prop (SProxy :: SProxy "gistErrorPaneVisible")

_currentView :: Lens' State View
_currentView = _Newtype <<< prop (SProxy :: SProxy "currentView")

_contractDemos :: Lens' State (Array ContractDemo)
_contractDemos = _Newtype <<< prop (SProxy :: SProxy "contractDemos")

_currentDemoName :: Lens' State (Maybe String)
_currentDemoName = _Newtype <<< prop (SProxy :: SProxy "currentDemoName")

_editorState :: Lens' State Editor.State
_editorState = _Newtype <<< prop (SProxy :: SProxy "editorState")

_simulations :: Lens' State (Cursor Simulation)
_simulations = _Newtype <<< prop (SProxy :: SProxy "simulations")

_actionDrag :: Lens' State (Maybe Int)
_actionDrag = _Newtype <<< prop (SProxy :: SProxy "actionDrag")

_simulationId :: Lens' Simulation Int
_simulationId = _Newtype <<< prop (SProxy :: SProxy "simulationId")

_simulationActions :: Lens' Simulation (Array (ContractCall FormArgument))
_simulationActions = _Newtype <<< prop (SProxy :: SProxy "simulationActions")

_simulationWallets :: Lens' Simulation (Array SimulatorWallet)
_simulationWallets = _Newtype <<< prop (SProxy :: SProxy "simulationWallets")

_evaluationResult :: Lens' State (WebData (Either PlaygroundError EvaluationResult))
_evaluationResult = _Newtype <<< prop (SProxy :: SProxy "evaluationResult")

_lastEvaluatedSimulation :: Lens' State (Maybe Simulation)
_lastEvaluatedSimulation = _Newtype <<< prop (SProxy :: SProxy "lastEvaluatedSimulation")

_resultRollup :: Lens' EvaluationResult (Array (Array AnnotatedTx))
_resultRollup = _Newtype <<< prop (SProxy :: SProxy "resultRollup")

_compilationResult :: Lens' State (WebData (Either InterpreterError (InterpreterResult CompilationResult)))
_compilationResult = _Newtype <<< prop (SProxy :: SProxy "compilationResult")

_successfulCompilationResult :: Traversal' State CompilationResult
_successfulCompilationResult = _compilationResult <<< _Success <<< _Right <<< _InterpreterResult <<< _result

_authStatus :: Lens' State (WebData AuthStatus)
_authStatus = _Newtype <<< prop (SProxy :: SProxy "authStatus")

_createGistResult :: Lens' State (WebData Gist)
_createGistResult = _Newtype <<< prop (SProxy :: SProxy "createGistResult")

_gistUrl :: Lens' State (Maybe String)
_gistUrl = _Newtype <<< prop (SProxy :: SProxy "gistUrl")

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

--- Language.Haskell.Interpreter ---
_result :: forall s a. Lens' { result :: a | s } a
_result = prop (SProxy :: SProxy "result")

_warnings :: forall s a. Lens' { warnings :: a | s } a
_warnings = prop (SProxy :: SProxy "warnings")

getKnownCurrencies :: forall m. MonadState State m => m (Array KnownCurrency)
getKnownCurrencies = fromMaybe [] <$> peruse (_successfulCompilationResult <<< _knownCurrencies)
