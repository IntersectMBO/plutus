module MainFrame.Lenses
  ( _demoFilesMenuVisible
  , _gistErrorPaneVisible
  , _currentView
  , _contractDemos
  , _currentDemoName
  , _editorState
  , _simulations
  , _actionDrag
  , _evaluationResult
  , _lastEvaluatedSimulation
  , _compilationResult
  , _successfulCompilationResult
  , _authStatus
  , _createGistResult
  , _gistUrl
  , _blockchainVisualisationState
  , _editorSlot
  , _balancesChartSlot
  , _contractDemoEditorContents
  , _simulationId
  , _simulationActions
  , _simulationWallets
  , _resultRollup
  , _functionSchema
  , _walletKeys
  , _knownCurrencies
  , _result
  , _warnings
  , getKnownCurrencies
  ) where

import Auth (AuthStatus)
import Chain.Types as Chain
import Control.Monad.State.Class (class MonadState)
import Cursor (Cursor)
import Data.Either (Either)
import Data.Json.JsonTuple (JsonTuple)
import Data.Lens (Lens', Traversal', _Right)
import Data.Lens.Extra (peruse)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe, fromMaybe)
import Data.Symbol (SProxy(..))
import Editor.Types (State) as Editor
import Gist (Gist)
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode, _InterpreterResult)
import MainFrame.Types (State, View, WebData)
import Network.RemoteData (_Success)
import Playground.Types (CompilationResult, ContractCall, ContractDemo, EvaluationResult, FunctionSchema, KnownCurrency, PlaygroundError, Simulation, SimulatorWallet)
import Plutus.V1.Ledger.Crypto (PubKeyHash)
import Prelude ((<$>), (<<<))
import Schema (FormSchema)
import Schema.Types (FormArgument)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Rollup.Types (AnnotatedTx)

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

_evaluationResult :: Lens' State (WebData (Either PlaygroundError EvaluationResult))
_evaluationResult = _Newtype <<< prop (SProxy :: SProxy "evaluationResult")

_lastEvaluatedSimulation :: Lens' State (Maybe Simulation)
_lastEvaluatedSimulation = _Newtype <<< prop (SProxy :: SProxy "lastEvaluatedSimulation")

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

_blockchainVisualisationState :: Lens' State Chain.State
_blockchainVisualisationState = _Newtype <<< prop (SProxy :: SProxy "blockchainVisualisationState")

------------------------------------------------------------
_editorSlot :: SProxy "editorSlot"
_editorSlot = SProxy

_balancesChartSlot :: SProxy "balancesChartSlot"
_balancesChartSlot = SProxy

------------------------------------------------------------
_contractDemoEditorContents :: Lens' ContractDemo SourceCode
_contractDemoEditorContents = _Newtype <<< prop (SProxy :: SProxy "contractDemoEditorContents")

_simulationId :: Lens' Simulation Int
_simulationId = _Newtype <<< prop (SProxy :: SProxy "simulationId")

_simulationActions :: Lens' Simulation (Array (ContractCall FormArgument))
_simulationActions = _Newtype <<< prop (SProxy :: SProxy "simulationActions")

_simulationWallets :: Lens' Simulation (Array SimulatorWallet)
_simulationWallets = _Newtype <<< prop (SProxy :: SProxy "simulationWallets")

_resultRollup :: Lens' EvaluationResult (Array (Array AnnotatedTx))
_resultRollup = _Newtype <<< prop (SProxy :: SProxy "resultRollup")

_functionSchema :: Lens' CompilationResult (Array (FunctionSchema FormSchema))
_functionSchema = _Newtype <<< prop (SProxy :: SProxy "functionSchema")

_walletKeys :: Lens' EvaluationResult (Array (JsonTuple PubKeyHash Wallet))
_walletKeys = _Newtype <<< prop (SProxy :: SProxy "walletKeys")

_knownCurrencies :: Lens' CompilationResult (Array KnownCurrency)
_knownCurrencies = _Newtype <<< prop (SProxy :: SProxy "knownCurrencies")

--- Language.Haskell.Interpreter ---
_result :: forall s a. Lens' { result :: a | s } a
_result = prop (SProxy :: SProxy "result")

_warnings :: forall s a. Lens' { warnings :: a | s } a
_warnings = prop (SProxy :: SProxy "warnings")

getKnownCurrencies :: forall m. MonadState State m => m (Array KnownCurrency)
getKnownCurrencies = fromMaybe [] <$> peruse (_successfulCompilationResult <<< _knownCurrencies)
