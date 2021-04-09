{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-

A live, multi-threaded PAB simulator with agent-specific states and actions
on them. Agents are represented by the 'Wallet' type. Each agent corresponds
to one PAB, with its own view of the world, all acting on the same blockchain.

-}
module Plutus.PAB.Simulator(
    Simulation
    , runSimulation
    -- * Run with user-defined contracts
    , SimulatorContractHandler
    , runSimulationWith
    , handleContractEffectMsg
    , SimulatorEffectHandlers
    , mkSimulatorHandlers
    , addWallet
    -- * Simulator actions
    , logString
    , logPretty
    -- ** Agent actions
    , payToWallet
    , activateContract
    , callEndpointOnInstance
    , handleAgentThread
    -- ** Control actions
    , makeBlock
    -- * Querying the state
    , instanceState
    , observableState
    , waitForState
    , activeEndpoints
    , waitForEndpoint
    , currentSlot
    , waitUntilSlot
    , waitNSlots
    , activeContracts
    , finalResult
    , waitUntilFinished
    , valueAt
    , valueAtSTM
    , blockchain
    -- ** Transaction counts
    , TxCounts(..)
    , txCounts
    , txValidated
    , txMemPool
    ) where

import qualified Cardano.Wallet.Mock                            as MockWallet
import           Control.Concurrent                             (forkIO)
import           Control.Concurrent.STM                         (STM, TQueue, TVar)
import qualified Control.Concurrent.STM                         as STM
import           Control.Lens                                   (_Just, at, makeLenses, makeLensesFor, preview, set,
                                                                 view, (&), (.~), (^.))
import           Control.Monad                                  (forever, void, when)
import           Control.Monad.Freer                            (Eff, LastMember, Member, interpret, reinterpret,
                                                                 reinterpret2, reinterpretN, run, send, type (~>))
import           Control.Monad.Freer.Delay                      (DelayEffect, delayThread, handleDelayEffect)
import           Control.Monad.Freer.Error                      (Error, handleError, throwError)
import           Control.Monad.Freer.Extras.Log                 (LogLevel (Info), LogMessage, LogMsg (..),
                                                                 handleLogWriter, logInfo, logLevel, mapLog)
import           Control.Monad.Freer.Reader                     (Reader, ask, asks)
import           Control.Monad.Freer.State                      (State (..), runState)
import           Control.Monad.Freer.Writer                     (Writer (..), runWriter)
import           Control.Monad.IO.Class                         (MonadIO (..))
import qualified Data.Aeson                                     as JSON
import           Data.Default                                   (Default (..))
import           Data.Foldable                                  (traverse_)
import           Data.Map                                       (Map)
import qualified Data.Map                                       as Map
import           Data.Semigroup                                 (Max (..))
import           Data.Set                                       (Set)
import           Data.Text                                      (Text)
import qualified Data.Text                                      as Text
import qualified Data.Text.IO                                   as Text
import           Data.Text.Prettyprint.Doc                      (Pretty (pretty), defaultLayoutOptions, layoutPretty)
import qualified Data.Text.Prettyprint.Doc.Render.Text          as Render
import           Data.Time.Units                                (Millisecond)
import           Ledger.Crypto                                  (PubKey, toPublicKey)
import qualified Ledger.Index                                   as UtxoIndex
import           Ledger.Tx                                      (Address, Tx, TxOut (..))
import           Ledger.Value                                   (Value)
import           Plutus.PAB.Core                                (EffectHandlers (..))
import qualified Plutus.PAB.Core                                as Core
import qualified Plutus.PAB.Core.ContractInstance.BlockchainEnv as BlockchainEnv
import           Plutus.PAB.Core.ContractInstance.STM           (BlockchainEnv, InstancesState, OpenEndpoint)
import qualified Plutus.PAB.Core.ContractInstance.STM           as Instances
import           Plutus.PAB.Effects.Contract                    (ContractStore)
import qualified Plutus.PAB.Effects.Contract                    as Contract
import           Plutus.PAB.Effects.Contract.Builtin            (Builtin)
import           Plutus.PAB.Effects.Contract.ContractTest       (TestContracts (..), handleContractTest)
import           Plutus.PAB.Effects.TimeEffect                  (TimeEffect)
import           Plutus.PAB.Monitoring.PABLogMsg                (ContractEffectMsg, PABMultiAgentMsg (..))
import           Plutus.PAB.Types                               (PABError (ContractInstanceNotFound, WalletError, WalletNotFound))
import           Plutus.PAB.Webserver.Types                     (ContractActivationArgs (..))
import           Plutus.V1.Ledger.Slot                          (Slot)
import qualified Wallet.API                                     as WAPI
import           Wallet.Effects                                 (ChainIndexEffect (..), NodeClientEffect (..),
                                                                 WalletEffect)
import qualified Wallet.Effects                                 as WalletEffects
import qualified Wallet.Emulator                                as Emulator
import           Wallet.Emulator.Chain                          (ChainControlEffect, ChainState)
import qualified Wallet.Emulator.Chain                          as Chain
import qualified Wallet.Emulator.ChainIndex                     as ChainIndex
import           Wallet.Emulator.MultiAgent                     (EmulatorEvent' (..), _singleton)
import           Wallet.Emulator.NodeClient                     (ChainClientNotification (..))
import qualified Wallet.Emulator.Stream                         as Emulator
import           Wallet.Emulator.Wallet                         (Wallet (..))
import qualified Wallet.Emulator.Wallet                         as Wallet
import           Wallet.Types                                   (ContractInstanceId, NotificationError)

-- | The current state of a contract instance
data SimulatorContractInstanceState t =
    SimulatorContractInstanceState
        { _contractDef   :: ContractActivationArgs (Contract.ContractDef t)
        , _contractState :: Contract.State t
        }

makeLensesFor [("_contractState", "contractState")] ''SimulatorContractInstanceState

data AgentState t =
    AgentState
        { _walletState :: Wallet.WalletState
        }

makeLenses ''AgentState

initialAgentState :: forall t. Wallet -> AgentState t
initialAgentState wallet =
    AgentState
        { _walletState = Wallet.emptyWalletState wallet
        }

data SimulatorState t =
    SimulatorState
        { _logMessages :: TQueue (LogMessage (PABMultiAgentMsg t))
        , _chainState  :: TVar ChainState
        , _agentStates :: TVar (Map Wallet (AgentState t))
        , _chainIndex  :: TVar ChainIndex.ChainIndexState
        , _instances   :: TVar (Map ContractInstanceId (SimulatorContractInstanceState t))
        }

makeLensesFor [("_logMessages", "logMessages"), ("_instances", "instances")] ''SimulatorState

initialState :: forall t. IO (SimulatorState t)
initialState = do
    let Emulator.EmulatorState{Emulator._chainState} = Emulator.initialState def
        initialWallets = Map.fromList $ fmap (\w -> (w, AgentState $ Wallet.emptyWalletState w)) $ Wallet <$> [1..10]
    STM.atomically $
        SimulatorState
            <$> STM.newTQueue
            <*> STM.newTVar _chainState
            <*> STM.newTVar initialWallets
            <*> STM.newTVar mempty
            <*> STM.newTVar mempty

-- | A handler for the 'ContractEffect' of @t@ that can run contracts in a
--   simulated environment.
type SimulatorContractHandler t =
    forall effs.
        ( Member (Error PABError) effs
        )
        => Eff (Contract.ContractEffect t ': effs)
        ~> Eff effs

type SimulatorEffectHandlers t = EffectHandlers t (SimulatorState t)

-- | Build 'EffectHandlers' for running a contract in the simulator
mkSimulatorHandlers ::
    forall t.
    Pretty (Contract.ContractDef t)
    => [Contract.ContractDef t] -- ^ Available contract definitions
    -> SimulatorContractHandler t -- ^ Making calls to the contract (see 'Plutus.PAB.Effects.Contract.ContractTest.handleContractTest' for an example)
    -> SimulatorEffectHandlers t
mkSimulatorHandlers definitions handleContractEffect =
    EffectHandlers
        { initialiseEnvironment =
            (,,)
                <$> liftIO (STM.atomically Instances.emptyInstancesState)
                <*> liftIO (STM.atomically Instances.emptyBlockchainEnv)
                <*> liftIO (initialState @t)
        , handleContractStoreEffect =
            interpret handleContractStore
        , handleContractEffect
        , handleLogMessages = handleLogSimulator @t
        , handleServicesEffects = handleServicesSimulator @t
        , handleContractDefinitionStoreEffect =
            interpret $ \case
                Contract.AddDefinition _ -> pure () -- not supported
                Contract.GetDefinitions  -> pure definitions
        , onStartup = do
            SimulatorState{_logMessages} <- Core.askUserEnv @t @(SimulatorState t)
            void $ liftIO $ forkIO (printLogMessages _logMessages)
            Core.PABRunner{Core.runPABAction} <- Core.pabRunner
            void
                $ liftIO
                $ forkIO
                $ void
                $ runPABAction
                $ handleDelayEffect
                $ interpret (Core.handleUserEnvReader @t @(SimulatorState t))
                $ interpret (Core.handleBlockchainEnvReader @t @(SimulatorState t))
                $ interpret (Core.handleInstancesStateReader @t @(SimulatorState t))
                $ advanceClock @t
            Core.waitUntilSlot 1
        , onShutdown = do
            handleDelayEffect $ delayThread (500 :: Millisecond) -- need to wait a little to avoid garbled terminal output in GHCi.
        }


-- | 'EffectHandlers' for running the PAB as a simulator (no connectivity to
--   out-of-process services such as wallet backend, node, etc.)
simulatorHandlers :: EffectHandlers (Builtin TestContracts) (SimulatorState (Builtin TestContracts))
simulatorHandlers = mkSimulatorHandlers @(Builtin TestContracts) [Game, Currency, AtomicSwap] handler where
    handler :: SimulatorContractHandler (Builtin TestContracts)
    handler = interpret handleContractTest

handleLogSimulator ::
    forall t effs.
    ( LastMember IO effs
    , Member (Reader (Core.PABEnvironment t (SimulatorState t))) effs
    )
    => Eff (LogMsg (PABMultiAgentMsg t) ': effs)
    ~> Eff effs
handleLogSimulator =
    interpret (logIntoTQueue @_ @(Core.PABEnvironment t (SimulatorState t)) @effs (view logMessages . Core.appEnv))

handleServicesSimulator ::
    forall t effs.
    ( Member (LogMsg (PABMultiAgentMsg t)) effs
    , Member (Reader (Core.PABEnvironment t (SimulatorState t))) effs
    , Member TimeEffect effs
    , LastMember IO effs
    , Member (Error PABError) effs
    )
    => Wallet
    -> Eff (WalletEffect ': ChainIndexEffect ': NodeClientEffect ': effs)
    ~> Eff effs
handleServicesSimulator wallet =
    let makeTimedChainIndexEvent wllt =
            interpret (mapLog @_ @(PABMultiAgentMsg t) EmulatorMsg)
            . reinterpret (Core.timed @EmulatorEvent')
            . reinterpret (mapLog (ChainIndexEvent wllt))
        makeTimedChainEvent =
            interpret (logIntoTQueue @_ @(Core.PABEnvironment t (SimulatorState t)) @effs (view logMessages . Core.appEnv))
            . reinterpret (mapLog @_ @(PABMultiAgentMsg t) EmulatorMsg)
            . reinterpret (Core.timed @EmulatorEvent' @(LogMsg Emulator.EmulatorEvent ': effs))
            . reinterpret (mapLog ChainEvent)
    in
        makeTimedChainEvent
        . interpret (Core.handleBlockchainEnvReader @t @(SimulatorState t))
        . interpret (Core.handleUserEnvReader @t @(SimulatorState t))
        . reinterpretN @'[Reader (SimulatorState t), Reader BlockchainEnv, LogMsg _] (handleChainEffect @t)
        . reinterpret handleNodeClient
        . makeTimedChainIndexEvent wallet
        . interpret (Core.handleUserEnvReader @t @(SimulatorState t))
        . reinterpretN @'[Reader (SimulatorState t), LogMsg _] (handleChainIndexEffect @t)

        . flip (handleError @WAPI.WalletAPIError) (throwError @PABError . WalletError)
        . interpret (Core.handleUserEnvReader @t @(SimulatorState t))
        . reinterpret (runWalletState @t wallet)
        . reinterpret2 @_ @(State Wallet.WalletState) @(Error WAPI.WalletAPIError) Wallet.handleWallet

-- | Convenience for wrapping 'ContractEffectMsg' in 'PABMultiAgentMsg t'
handleContractEffectMsg :: forall t x effs. Member (LogMsg (PABMultiAgentMsg t)) effs => Eff (LogMsg ContractEffectMsg ': effs) x -> Eff effs x
handleContractEffectMsg = interpret (mapLog @_ @(PABMultiAgentMsg t) ContractMsg)

-- | Handle the 'State WalletState' effect by reading from and writing
--   to a TVar in the 'SimulatorState'
runWalletState ::
    forall t effs.
    ( LastMember IO effs
    , Member (Error PABError) effs
    , Member (Reader (SimulatorState t)) effs
    )
    => Wallet
    -> State Wallet.WalletState
    ~> Eff effs
runWalletState wallet = \case
    Get -> do
        SimulatorState{_agentStates} <- ask @(SimulatorState t)
        result <- liftIO $ STM.atomically $ do
            mp <- STM.readTVar _agentStates
            pure $ Map.lookup wallet mp
        case result of
            Nothing -> throwError $ WalletNotFound wallet
            Just s  -> pure (_walletState s)
    Put s -> do
        SimulatorState{_agentStates} <- ask @(SimulatorState t)
        liftIO $ STM.atomically $ do
            mp <- STM.readTVar _agentStates
            case Map.lookup wallet mp of
                Nothing -> do
                    let newState = initialAgentState wallet & walletState .~ s
                    STM.writeTVar _agentStates (Map.insert wallet newState mp)
                Just s' -> do
                    let newState = s' & walletState .~ s
                    STM.writeTVar _agentStates (Map.insert wallet newState mp)

-- | Make a payment to a wallet
payToWallet :: Member WalletEffect effs => Wallet -> Value -> Eff effs Tx
payToWallet target amount = WAPI.payToPublicKey WAPI.defaultSlotRange amount (Emulator.walletPubKey target)

-- | Start a new instance of a contract
activateContract :: forall t. Contract.PABContract t => Wallet -> Contract.ContractDef t -> Simulation t ContractInstanceId
activateContract = Core.activateContract

-- | Call a named endpoint on a contract instance
callEndpointOnInstance :: forall a t. (JSON.ToJSON a) => ContractInstanceId -> String -> a -> Simulation t (Maybe NotificationError)
callEndpointOnInstance = Core.callEndpointOnInstance

-- | Log some output to the console
logString :: forall t effs. Member (LogMsg (PABMultiAgentMsg t)) effs => String -> Eff effs ()
logString = logInfo @(PABMultiAgentMsg t) . UserLog . Text.pack

-- | Pretty-prin a value to the console
logPretty :: forall a t effs. (Pretty a, Member (LogMsg (PABMultiAgentMsg t)) effs) => a -> Eff effs ()
logPretty = logInfo @(PABMultiAgentMsg t) . UserLog . render

-- | Wait 1 second, then add a new block.
makeBlock ::
    forall t effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState t)) effs
    , Member (Reader InstancesState) effs
    , Member (Reader BlockchainEnv) effs
    , Member DelayEffect effs
    , Member TimeEffect effs
    ) => Eff effs ()
makeBlock = do
    let makeTimedChainEvent =
            interpret (logIntoTQueue @_ @(SimulatorState t) (view logMessages))
            . reinterpret (mapLog @_ @(PABMultiAgentMsg t) EmulatorMsg)
            . reinterpret (Core.timed @EmulatorEvent')
            . reinterpret (mapLog ChainEvent)
        makeTimedChainIndexEvent =
            interpret (logIntoTQueue @_ @(SimulatorState t) (view logMessages))
            . reinterpret (mapLog @_ @(PABMultiAgentMsg t) EmulatorMsg)
            . reinterpret (Core.timed @EmulatorEvent')
            . reinterpret (mapLog (ChainIndexEvent (Wallet 0)))
    delayThread (1000 :: Millisecond)
    void
        $ makeTimedChainIndexEvent
        $ makeTimedChainEvent
        $ interpret (handleChainIndexControlEffect @t)
        $ interpret (handleChainControl @t)
        $ Chain.processBlock

-- | Get the current state of the contract instance.
instanceState :: forall t. Wallet -> ContractInstanceId -> Simulation t (Contract.State t)
instanceState = Core.instanceState

-- | An STM transaction that returns the observable state of the contract instance.
observableState :: forall t. ContractInstanceId -> Simulation t (STM JSON.Value)
observableState = Core.observableState

-- | Wait until the observable state of the instance matches a predicate.
waitForState :: forall t a. (JSON.Value -> Maybe a) -> ContractInstanceId -> Simulation t a
waitForState = Core.waitForState

-- | The list of endpoints that are currently open
activeEndpoints :: forall t. ContractInstanceId -> Simulation t (STM [OpenEndpoint])
activeEndpoints = Core.activeEndpoints

-- | The final result of the instance (waits until it is available)
finalResult :: forall t. ContractInstanceId -> Simulation t (STM (Maybe JSON.Value))
finalResult = Core.finalResult

-- | Wait until the contract is done, then return
--   the error (if any)
waitUntilFinished :: forall t. ContractInstanceId -> Simulation t (Maybe JSON.Value)
waitUntilFinished = Core.waitUntilFinished

-- | Wait until the endpoint becomes active.
waitForEndpoint :: forall t. ContractInstanceId -> String -> Simulation t ()
waitForEndpoint = Core.waitForEndpoint

currentSlot :: forall t. Simulation t (STM Slot)
currentSlot = Core.currentSlot

-- | Wait until the target slot number has been reached
waitUntilSlot :: forall t. Slot -> Simulation t ()
waitUntilSlot = Core.waitUntilSlot

-- | Wait for the given number of slots.
waitNSlots :: forall t. Int -> Simulation t ()
waitNSlots = Core.waitNSlots

type Simulation t a = Core.PABAction t (SimulatorState t) a

runSimulation :: Simulation (Builtin TestContracts) a -> IO (Either PABError a)
runSimulation = runSimulationWith @(Builtin TestContracts) simulatorHandlers

runSimulationWith :: SimulatorEffectHandlers t -> Simulation t a -> IO (Either PABError a)
runSimulationWith handlers = Core.runPAB handlers

-- | Handle a 'LogMsg' effect in terms of a "larger" 'State' effect from which we have a setter.
logIntoTQueue ::
    forall s1 s2 effs.
    ( Member (Reader s2) effs
    , LastMember IO effs
    )
    => (s2 -> TQueue (LogMessage s1))
    -> LogMsg s1
    ~> Eff effs
logIntoTQueue f = \case
    LMessage w -> do
        tv <- asks f
        liftIO $ STM.atomically $ STM.writeTQueue tv w

handleChainControl ::
    forall t effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState t)) effs
    , Member (Reader BlockchainEnv) effs
    , Member (Reader InstancesState) effs
    , Member (LogMsg Chain.ChainEvent) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    )
    => ChainControlEffect
    ~> Eff effs
handleChainControl = \case
    Chain.ProcessBlock -> do
        blockchainEnv <- ask @BlockchainEnv
        instancesState <- ask @InstancesState
        (txns, slot) <- runChainEffects @t @_ $ do
                txns <- Chain.processBlock
                sl <- Chain.getCurrentSlot
                pure (txns, sl)
        runChainIndexEffects @t $ do
            ChainIndex.chainIndexNotify $ BlockValidated txns
            ChainIndex.chainIndexNotify $ SlotChanged slot

        void $ liftIO $ STM.atomically $ do
            cenv <- BlockchainEnv.getClientEnv instancesState
            BlockchainEnv.updateInterestingAddresses blockchainEnv cenv
            BlockchainEnv.processBlock blockchainEnv txns slot

        pure txns

runChainEffects ::
    forall t a effs.
    ( Member (Reader (SimulatorState t)) effs
    , Member (LogMsg Chain.ChainEvent) effs
    , LastMember IO effs
    )
    => Eff (Chain.ChainEffect ': Chain.ChainControlEffect ': Chain.ChainEffs) a
    -> Eff effs a
runChainEffects action = do
    SimulatorState{_chainState} <- ask @(SimulatorState t)
    (a, logs) <- liftIO $ STM.atomically $ do
                        oldState <- STM.readTVar _chainState
                        let ((a, newState), logs) =
                                run
                                $ runWriter @[LogMessage Chain.ChainEvent]
                                $ reinterpret @(LogMsg Chain.ChainEvent) @(Writer [LogMessage Chain.ChainEvent]) (handleLogWriter _singleton)
                                $ runState oldState
                                $ interpret Chain.handleControlChain
                                $ interpret Chain.handleChain
                                $ action
                        STM.writeTVar _chainState newState
                        pure (a, logs)
    traverse_ (send . LMessage) logs
    pure a

runChainIndexEffects ::
    forall t a m effs.
    ( Member (Reader (SimulatorState t)) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    , LastMember m effs
    , MonadIO m
    )
    => Eff (ChainIndexEffect ': ChainIndex.ChainIndexControlEffect ': ChainIndex.ChainIndexEffs) a
    -> Eff effs a
runChainIndexEffects action = do
    SimulatorState{_chainIndex} <- ask @(SimulatorState t)
    (a, logs) <- liftIO $ STM.atomically $ do
                    oldState <- STM.readTVar _chainIndex
                    let ((a, newState), logs) =
                            run
                            $ runWriter @[LogMessage ChainIndex.ChainIndexEvent]
                            $ reinterpret @(LogMsg ChainIndex.ChainIndexEvent) @(Writer [LogMessage ChainIndex.ChainIndexEvent]) (handleLogWriter _singleton)
                            $ runState oldState
                            $ ChainIndex.handleChainIndexControl
                            $ ChainIndex.handleChainIndex
                            $ action
                    STM.writeTVar _chainIndex newState
                    pure (a, logs)
    traverse_ (send . LMessage) logs
    pure a

-- | Handle the 'NodeClientEffect' using the 'SimulatorState'.
handleNodeClient ::
    forall effs.
    ( Member Chain.ChainEffect effs
    )
    => NodeClientEffect
    ~> Eff effs
handleNodeClient = \case
    PublishTx tx  -> Chain.queueTx tx
    GetClientSlot -> Chain.getCurrentSlot

-- | Handle the 'Chain.ChainEffect' using the 'SimulatorState'.
handleChainEffect ::
    forall t effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState t)) effs
    , Member (LogMsg Chain.ChainEvent) effs
    )
    => Chain.ChainEffect
    ~> Eff effs
handleChainEffect = \case
    Chain.QueueTx tx     -> runChainEffects @t $ Chain.queueTx tx
    Chain.GetCurrentSlot -> runChainEffects @t $ Chain.getCurrentSlot

handleChainIndexEffect ::
    forall t effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState t)) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    )
    => ChainIndexEffect
    ~> Eff effs
handleChainIndexEffect = runChainIndexEffects @t . \case
    StartWatching a           -> WalletEffects.startWatching a
    WatchedAddresses          -> WalletEffects.watchedAddresses
    ConfirmedBlocks           -> WalletEffects.confirmedBlocks
    TransactionConfirmed txid -> WalletEffects.transactionConfirmed txid
    NextTx r                  -> WalletEffects.nextTx r

handleChainIndexControlEffect ::
    forall t effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState t)) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    )
    => ChainIndex.ChainIndexControlEffect
    ~> Eff effs
handleChainIndexControlEffect = runChainIndexEffects @t . \case
    ChainIndex.ChainIndexNotify n -> ChainIndex.chainIndexNotify n

-- | Start a thread that prints log messages to the terminal when they come in.
printLogMessages ::
    forall t.
    Pretty t
    => TQueue (LogMessage t) -- ^ log messages
    -> IO ()
printLogMessages queue = void $ forkIO $ forever $ do
    msg <- STM.atomically $ STM.readTQueue queue
    when (msg ^. logLevel >= Info) (Text.putStrLn (render msg))

-- | Call 'makeBlock' forever.
advanceClock ::
    forall t effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState t)) effs
    , Member (Reader InstancesState) effs
    , Member (Reader BlockchainEnv) effs
    , Member DelayEffect effs
    , Member TimeEffect effs
    )
    => Eff effs ()
advanceClock = forever (makeBlock @t)

-- | Handle the 'ContractStore' effect by writing the state to the
--   TVar in 'SimulatorState'
handleContractStore ::
    forall t effs.
    ( LastMember IO effs
    , Member (Reader (Core.PABEnvironment t (SimulatorState t))) effs
    , Member (Error PABError) effs
    )
    => ContractStore t
    ~> Eff effs
handleContractStore = \case
    Contract.PutState definition instanceId state -> do
        instancesTVar <- view instances <$> (Core.askUserEnv @t @(SimulatorState t))
        liftIO $ STM.atomically $ do
            let instState = SimulatorContractInstanceState{_contractDef = definition, _contractState = state}
            STM.modifyTVar instancesTVar (set (at instanceId) (Just instState))
    Contract.GetState instanceId -> do
        instancesTVar <- view instances <$> (Core.askUserEnv @t @(SimulatorState t))
        result <- preview (at instanceId . _Just . contractState) <$> liftIO (STM.readTVarIO instancesTVar)
        case result of
            Just s  -> pure s
            Nothing -> throwError (ContractInstanceNotFound instanceId)
    Contract.ActiveContracts -> do
        instancesTVar <- view instances <$> (Core.askUserEnv @t @(SimulatorState t))
        fmap _contractDef <$> liftIO (STM.readTVarIO instancesTVar)

render :: forall a. Pretty a => a -> Text
render = Render.renderStrict . layoutPretty defaultLayoutOptions . pretty


-- | Statistics about the transactions that have been validated by the emulated
--   node.
data TxCounts =
    TxCounts
        { _txValidated :: Int
        -- ^ How many transactions were checked and added to the ledger
        , _txMemPool   :: Int
        -- ^ How many transactions remain in the mempool of the emulated node
        } deriving (Eq, Ord, Show)

makeLenses ''TxCounts

-- | Get the 'TxCounts' of the emulated blockchain
txCounts :: forall t. Simulation t TxCounts
txCounts = do
    SimulatorState{_chainState} <- Core.askUserEnv @t @(SimulatorState t)
    Chain.ChainState{Chain._chainNewestFirst, Chain._txPool} <- liftIO $ STM.readTVarIO _chainState
    return
        $ TxCounts
            { _txValidated = sum (length <$> _chainNewestFirst)
            , _txMemPool   = length _txPool
            }

-- | The set of all active contracts.
activeContracts :: forall t. Simulation t (Set ContractInstanceId)
activeContracts = Core.activeContracts

-- | The total value currently at an address
valueAtSTM :: forall t. Address -> Simulation t (STM Value)
valueAtSTM address = do
    SimulatorState{_chainState} <- Core.askUserEnv @t @(SimulatorState t)
    pure $ do
        Chain.ChainState{Chain._index=UtxoIndex.UtxoIndex mp} <- STM.readTVar _chainState
        pure $ foldMap txOutValue $ filter (\TxOut{txOutAddress} -> txOutAddress == address) $ fmap snd $ Map.toList mp

-- | The total value currently at an address
valueAt :: forall t. Address -> Simulation t Value
valueAt address = do
    stm <- valueAtSTM address
    liftIO $ STM.atomically stm

-- | The entire chain (newest transactions first)
blockchain :: forall t. Simulation t [[Tx]]
blockchain = do
    SimulatorState{_chainState} <- Core.askUserEnv @t @(SimulatorState t)
    Chain.ChainState{Chain._chainNewestFirst} <- liftIO $ STM.readTVarIO _chainState
    pure _chainNewestFirst

handleAgentThread ::
    forall t a.
    Wallet
    -> Eff (Core.ContractInstanceEffects t (SimulatorState t) '[IO]) a
    -> Simulation t a
handleAgentThread = Core.handleAgentThread

-- | Create a new wallet with a random key and add it to the list of simulated wallets
addWallet :: forall t. Simulation t (Wallet, PubKey)
addWallet = do
    SimulatorState{_agentStates} <- Core.askUserEnv @t @(SimulatorState t)
    (_, privateKey) <- MockWallet.newKeyPair
    liftIO $ STM.atomically $ do
        currentWallets <- STM.readTVar _agentStates
        let newWalletId = maybe 0 (succ . getMax) $ foldMap (Just . Max . getWallet) $ Map.keysSet currentWallets
            newWallet = Wallet newWalletId
            newWallets = currentWallets & at newWallet .~ Just (AgentState $ Wallet.emptyWalletStateFromPrivateKey privateKey)
        STM.writeTVar _agentStates newWallets
        pure (newWallet, toPublicKey privateKey)
