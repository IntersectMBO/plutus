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
    runSimulation
    , Simulation
    -- * Simulator actions
    , logString
    , logPretty
    -- ** Agent actions
    , payToWallet
    , activateContract
    , callEndpointOnInstance
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
    , blockchain
    -- ** Transaction counts
    , TxCounts(..)
    , txCounts
    , txValidated
    , txMemPool
    -- * Types
    , SimulatorState(..)
    , initialState
    , chainState
    , agentStates
    , chainIndex
    , instances
    , contractDef
    -- * Agents
    , AgentState(..)
    , initialAgentState
    ) where

import           Control.Applicative                             (Alternative (..))
import           Control.Concurrent                              (forkIO)
import           Control.Concurrent.STM                          (STM, TQueue, TVar)
import qualified Control.Concurrent.STM                          as STM
import           Control.Lens                                    (Lens', _Just, anon, at, makeLenses, preview, set,
                                                                  view, (&), (.~), (^.))
import           Control.Monad                                   (forever, guard, void, when)
import           Control.Monad.Freer                             (Eff, LastMember, Member, interpret, reinterpret,
                                                                  reinterpret2, reinterpretN, run, send, type (~>))
import           Control.Monad.Freer.Delay                       (DelayEffect, delayThread, handleDelayEffect)
import           Control.Monad.Freer.Error                       (Error, handleError, throwError)
import           Control.Monad.Freer.Extras.Log                  (LogLevel (Info), LogMessage, LogMsg (..),
                                                                  handleLogWriter, logInfo, logLevel, mapLog)
import           Control.Monad.Freer.Reader                      (Reader, ask, asks)
import           Control.Monad.Freer.State                       (State (..), runState)
import           Control.Monad.Freer.Writer                      (Writer (..), runWriter)
import           Control.Monad.IO.Class                          (MonadIO (..))
import qualified Data.Aeson                                      as JSON
import           Data.Foldable                                   (traverse_)
import           Data.Map                                        (Map)
import qualified Data.Map                                        as Map
import           Data.Set                                        (Set)
import           Data.Text                                       (Text)
import qualified Data.Text                                       as Text
import qualified Data.Text.IO                                    as Text
import           Data.Text.Prettyprint.Doc                       (Pretty (pretty), defaultLayoutOptions, layoutPretty)
import qualified Data.Text.Prettyprint.Doc.Render.Text           as Render
import           Data.Time.Units                                 (Millisecond)
import           Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint (..))
import qualified Ledger.Index                                    as UtxoIndex
import           Ledger.Tx                                       (Address, Tx, TxOut (..))
import           Ledger.Value                                    (Value)
import           Plutus.PAB.Core                                 (EffectHandlers (..))
import qualified Plutus.PAB.Core                                 as Core
import qualified Plutus.PAB.Core.ContractInstance.BlockchainEnv  as BlockchainEnv
import           Plutus.PAB.Core.ContractInstance.STM            (BlockchainEnv, InstancesState, OpenEndpoint)
import qualified Plutus.PAB.Core.ContractInstance.STM            as Instances
import           Plutus.PAB.Effects.Contract                     (ContractStore)
import qualified Plutus.PAB.Effects.Contract                     as Contract
import           Plutus.PAB.Effects.Contract.ContractTest        (TestContracts (..), handleContractTest)
import           Plutus.PAB.Effects.TimeEffect                   (TimeEffect)
import           Plutus.PAB.Monitoring.PABLogMsg                 (ContractEffectMsg, PABMultiAgentMsg (..))
import           Plutus.PAB.Types                                (PABError (ContractInstanceNotFound, WalletError))
import           Plutus.V1.Ledger.Slot                           (Slot)
import qualified Wallet.API                                      as WAPI
import           Wallet.Effects                                  (ChainIndexEffect (..), NodeClientEffect (..),
                                                                  WalletEffect)
import qualified Wallet.Effects                                  as WalletEffects
import qualified Wallet.Emulator                                 as Emulator
import           Wallet.Emulator.Chain                           (ChainControlEffect, ChainState)
import qualified Wallet.Emulator.Chain                           as Chain
import qualified Wallet.Emulator.ChainIndex                      as ChainIndex
import           Wallet.Emulator.MultiAgent                      (EmulatorEvent' (..), _singleton)
import           Wallet.Emulator.NodeClient                      (ChainClientNotification (..))
import qualified Wallet.Emulator.Stream                          as Emulator
import           Wallet.Emulator.Wallet                          (Wallet (..))
import qualified Wallet.Emulator.Wallet                          as Wallet
import           Wallet.Types                                    (ContractInstanceId, EndpointDescription (..),
                                                                  NotificationError)


-- | The current state of a contract instance
data SimulatorContractInstanceState t =
    SimulatorContractInstanceState
        { _contractDef   :: Contract.ContractDef t
        , _contractState :: Contract.State t
        }

makeLenses ''SimulatorContractInstanceState

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

makeLenses ''SimulatorState

initialState :: forall t. IO (SimulatorState t)
initialState = do
    let Emulator.EmulatorState{Emulator._chainState} = Emulator.initialState Emulator.defaultEmulatorConfig
    STM.atomically $
        SimulatorState
            <$> STM.newTQueue
            <*> STM.newTVar _chainState
            <*> STM.newTVar mempty
            <*> STM.newTVar mempty
            <*> STM.newTVar mempty


-- | 'EffectHandlers' for running the PAB as a simulator (no connectivity to
--   out-of-process services such as wallet backend, node, etc.)
simulatorHandlers :: EffectHandlers TestContracts (SimulatorState TestContracts)
simulatorHandlers =
    EffectHandlers
        { initialiseEnvironment =
            (,,)
                <$> liftIO (STM.atomically Instances.emptyInstancesState)
                <*> liftIO (STM.atomically Instances.emptyBlockchainEnv)
                <*> liftIO (initialState @TestContracts)
        , handleContractStoreEffect =
            interpret handleContractStore
        , handleContractEffect =
            handleContractEffectMsg @TestContracts
            . reinterpret handleContractTest
        , handleLogMessages = handleLogSimulator
        , handleServicesEffects = handleServicesSimulator
        , handleContractDefinitionStoreEffect =
            interpret $ \case
                Contract.AddDefinition _ -> pure () -- not supported
                Contract.GetDefinitions  -> pure [Game, Currency, AtomicSwap]
        , onStartup = do
            SimulatorState{_logMessages} <- Core.userEnv @TestContracts @(SimulatorState TestContracts)
            void $ liftIO $ forkIO (printLogMessages _logMessages)
            Core.PABRunner{Core.runPABAction} <- Core.pabRunner
            void
                $ liftIO
                $ forkIO
                $ void
                $ runPABAction
                $ handleDelayEffect
                $ interpret (Core.handleUserEnvReader @TestContracts @(SimulatorState TestContracts))
                $ interpret (Core.handleBlockchainEnvReader @TestContracts @(SimulatorState TestContracts))
                $ interpret (Core.handleInstancesStateReader @TestContracts @(SimulatorState TestContracts))
                $ advanceClock
            Core.waitUntilSlot 1
        , onShutdown = do
            handleDelayEffect $ delayThread (500 :: Millisecond) -- need to wait a little to avoid garbled terminal output in GHCi.
        }

handleLogSimulator ::
    forall effs.
    ( LastMember IO effs
    , Member (Reader (Core.PABEnvironment TestContracts (SimulatorState TestContracts))) effs
    )
    => Eff (LogMsg (PABMultiAgentMsg TestContracts) ': effs)
    ~> Eff effs
handleLogSimulator =
    interpret (logIntoTQueue @_ @(Core.PABEnvironment TestContracts (SimulatorState TestContracts)) @effs (view logMessages . Core.appEnv))

handleServicesSimulator ::
    forall effs.
    ( Member (LogMsg (PABMultiAgentMsg TestContracts)) effs
    , Member (Reader (Core.PABEnvironment TestContracts (SimulatorState TestContracts))) effs
    , Member TimeEffect effs
    , LastMember IO effs
    , Member (Error PABError) effs
    )
    => Wallet
    -> Eff (WalletEffect ': ChainIndexEffect ': NodeClientEffect ': effs)
    ~> Eff effs
handleServicesSimulator wallet =
    let makeTimedChainIndexEvent wllt =
            interpret (mapLog @_ @(PABMultiAgentMsg TestContracts) EmulatorMsg)
            . reinterpret (Core.timed @EmulatorEvent')
            . reinterpret (mapLog (ChainIndexEvent wllt))
        makeTimedChainEvent =
            interpret (logIntoTQueue @_ @(Core.PABEnvironment TestContracts (SimulatorState TestContracts)) @effs (view logMessages . Core.appEnv))
            . reinterpret (mapLog @_ @(PABMultiAgentMsg TestContracts) EmulatorMsg)
            . reinterpret (Core.timed @EmulatorEvent' @(LogMsg Emulator.EmulatorEvent ': effs))
            . reinterpret (mapLog ChainEvent)
    in
        makeTimedChainEvent
        . interpret (Core.handleBlockchainEnvReader @TestContracts @(SimulatorState TestContracts))
        . interpret (Core.handleUserEnvReader @TestContracts @(SimulatorState TestContracts))
        . reinterpretN @'[Reader (SimulatorState TestContracts), Reader BlockchainEnv, LogMsg _] handleChainEffect
        . reinterpret handleNodeClient
        . makeTimedChainIndexEvent wallet
        . interpret (Core.handleUserEnvReader @TestContracts @(SimulatorState TestContracts))
        . reinterpretN @'[Reader (SimulatorState TestContracts), LogMsg _] handleChainIndexEffect

        . flip (handleError @WAPI.WalletAPIError) (throwError @PABError . WalletError)
        . interpret (Core.handleUserEnvReader @TestContracts @(SimulatorState TestContracts))
        . reinterpret (runWalletState wallet)
        . reinterpret2 @_ @(State Wallet.WalletState) @(Error WAPI.WalletAPIError) Wallet.handleWallet

handleContractEffectMsg :: forall t x effs. Member (LogMsg (PABMultiAgentMsg t)) effs => Eff (LogMsg ContractEffectMsg ': effs) x -> Eff effs x
handleContractEffectMsg = interpret (mapLog @_ @(PABMultiAgentMsg t) ContractMsg)

-- | Handle the 'State WalletState' effect by reading from and writing
--   to a TVar in the 'SimulatorState'
runWalletState ::
    forall effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
    )
    => Wallet
    -> State Wallet.WalletState
    ~> Eff effs
runWalletState wallet = \case
    Get -> do
        SimulatorState{_agentStates} <- ask @(SimulatorState TestContracts)
        liftIO $ STM.atomically $ do
            mp <- STM.readTVar _agentStates
            case Map.lookup wallet mp of
                Nothing -> do
                    let newState = initialAgentState wallet
                    STM.writeTVar _agentStates (Map.insert wallet newState mp)
                    pure (_walletState newState)
                Just s -> pure (_walletState s)
    Put s -> do
        SimulatorState{_agentStates} <- ask @(SimulatorState TestContracts)
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
activateContract :: Wallet -> TestContracts -> Simulation ContractInstanceId
activateContract = Core.activateContract

-- | Call a named endpoint on a contract instance
callEndpointOnInstance :: forall a. (JSON.ToJSON a) => ContractInstanceId -> String -> a -> Simulation (Maybe NotificationError)
callEndpointOnInstance = Core.callEndpointOnInstance

-- | Log some output to the console
logString :: forall t effs. Member (LogMsg (PABMultiAgentMsg t)) effs => String -> Eff effs ()
logString = logInfo @(PABMultiAgentMsg t) . UserLog . Text.pack

-- | Pretty-prin a value to the console
logPretty :: forall a t effs. (Pretty a, Member (LogMsg (PABMultiAgentMsg t)) effs) => a -> Eff effs ()
logPretty = logInfo @(PABMultiAgentMsg t) . UserLog . render

-- | Wait 0.2 seconds, then add a new block.
makeBlock ::
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (Reader InstancesState) effs
    , Member (Reader BlockchainEnv) effs
    , Member DelayEffect effs
    , Member TimeEffect effs
    ) => Eff effs ()
makeBlock = do
    let makeTimedChainEvent =
            interpret (logIntoTQueue @_ @(SimulatorState TestContracts) (view logMessages))
            . reinterpret (mapLog @_ @(PABMultiAgentMsg TestContracts) EmulatorMsg)
            . reinterpret (Core.timed @EmulatorEvent')
            . reinterpret (mapLog ChainEvent)
        makeTimedChainIndexEvent =
            interpret (logIntoTQueue @_ @(SimulatorState TestContracts) (view logMessages))
            . reinterpret (mapLog @_ @(PABMultiAgentMsg TestContracts) EmulatorMsg)
            . reinterpret (Core.timed @EmulatorEvent')
            . reinterpret (mapLog (ChainIndexEvent (Wallet 0)))
    delayThread (200 :: Millisecond)
    void
        $ makeTimedChainIndexEvent
        $ makeTimedChainEvent
        $ interpret handleChainIndexControlEffect
        $ interpret handleChainControl
        $ Chain.processBlock

-- | Get the current state of the contract instance.
instanceState ::
    Wallet
    -> ContractInstanceId
    -> Simulation (Contract.State TestContracts)
instanceState = Core.instanceState

-- | An STM transaction that returns the observable state of the contract instance.
observableState ::
    forall effs.
    ( Member (Reader InstancesState) effs )
    => ContractInstanceId
    -> Eff effs (STM JSON.Value)
observableState instanceId = do
    instancesState <- ask @InstancesState
    pure $ Instances.obervableContractState instanceId instancesState

-- | Wait until the observable state of the instance matches a predicate.
waitForState ::
    forall a effs.
    ( Member (Reader InstancesState) effs
    , LastMember IO effs
    )
    => (JSON.Value -> Maybe a)
    -> ContractInstanceId
    -> Eff effs a
waitForState extract instanceId = do
    stm <- observableState instanceId
    liftIO $ STM.atomically $ do
        state <- stm
        case extract state of
            Nothing -> empty
            Just k  -> pure k

-- | The list of endpoints that are currently open
activeEndpoints ::
    forall effs.
    ( Member (Reader InstancesState) effs)
    => ContractInstanceId
    -> Eff effs (STM [OpenEndpoint])
activeEndpoints instanceId = do
    instancesState <- ask @InstancesState
    pure $ do
        is <- Instances.instanceState instanceId instancesState
        fmap snd . Map.toList <$> Instances.openEndpoints is

-- | The final result of the instance (waits until it is available)
finalResult ::
    forall effs.
    ( Member (Reader InstancesState) effs)
    => ContractInstanceId
    -> Eff effs (STM (Maybe JSON.Value))
finalResult instanceId = do
    instancesState <- ask @InstancesState
    pure $ Instances.finalResult instanceId instancesState

-- | Wait until the contract is done, then return
--   the error (if any)
waitUntilFinished ::
    forall effs.
    ( Member (Reader InstancesState) effs
    , LastMember IO effs
    )
    => ContractInstanceId
    -> Eff effs (Maybe JSON.Value)
waitUntilFinished i =
    finalResult i >>= liftIO . STM.atomically

-- | Wait until the endpoint becomes active.
waitForEndpoint ::
    forall effs.
    ( Member (Reader InstancesState) effs
    , LastMember IO effs
    )
    => ContractInstanceId
    -> String
    -> Eff effs ()
waitForEndpoint instanceId endpointName = do
    tx <- activeEndpoints instanceId
    liftIO $ STM.atomically $ do
        eps <- tx
        guard $ any (\Instances.OpenEndpoint{Instances.oepName=ActiveEndpoint{aeDescription=EndpointDescription nm}} -> nm == endpointName) eps

currentSlot ::
    forall effs.
    ( Member (Reader BlockchainEnv) effs
    )
    => Eff effs (STM Slot)
currentSlot = do
    Instances.BlockchainEnv{Instances.beCurrentSlot} <- ask
    pure $ STM.readTVar beCurrentSlot

-- | Wait until the target slot number has been reached
waitUntilSlot ::
    forall effs.
    ( Member (Reader BlockchainEnv) effs
    , LastMember IO effs
    )
    => Slot
    -> Eff effs ()
waitUntilSlot targetSlot = do
    tx <- currentSlot
    void $ liftIO $ STM.atomically $ do
        s <- tx
        guard (s >= targetSlot)

waitNSlots ::
    forall effs.
    ( Member (Reader BlockchainEnv) effs
    , LastMember IO effs
    )
    => Int
    -> Eff effs ()
waitNSlots i = do
    current <- currentSlot >>= liftIO . STM.atomically
    waitUntilSlot (current + fromIntegral i)

type Simulation a = Core.PABAction TestContracts (SimulatorState TestContracts) a

runSimulation :: Simulation a -> IO (Either PABError a)
runSimulation = Core.runPAB simulatorHandlers

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
    forall effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
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
        (txns, slot) <- runChainEffects @_ $ do
                txns <- Chain.processBlock
                sl <- Chain.getCurrentSlot
                pure (txns, sl)
        runChainIndexEffects $ do
            ChainIndex.chainIndexNotify $ BlockValidated txns
            ChainIndex.chainIndexNotify $ SlotChanged slot

        void $ liftIO $ STM.atomically $ do
            cenv <- BlockchainEnv.getClientEnv instancesState
            BlockchainEnv.updateInterestingAddresses blockchainEnv cenv
            BlockchainEnv.processBlock blockchainEnv txns slot

        pure txns

runChainEffects ::
    forall a effs.
    ( Member (Reader (SimulatorState TestContracts)) effs
    , Member (LogMsg Chain.ChainEvent) effs
    , LastMember IO effs
    )
    => Eff (Chain.ChainEffect ': Chain.ChainControlEffect ': Chain.ChainEffs) a
    -> Eff effs a
runChainEffects action = do
    SimulatorState{_chainState} <- ask @(SimulatorState TestContracts)
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
    forall a m effs.
    ( Member (Reader (SimulatorState TestContracts)) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    , LastMember m effs
    , MonadIO m
    )
    => Eff (ChainIndexEffect ': ChainIndex.ChainIndexControlEffect ': ChainIndex.ChainIndexEffs) a
    -> Eff effs a
runChainIndexEffects action = do
    SimulatorState{_chainIndex} <- ask @(SimulatorState TestContracts)
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
    forall effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (LogMsg Chain.ChainEvent) effs
    )
    => Chain.ChainEffect
    ~> Eff effs
handleChainEffect = \case
    Chain.QueueTx tx     -> runChainEffects $ Chain.queueTx tx
    Chain.GetCurrentSlot -> runChainEffects $ Chain.getCurrentSlot

handleChainIndexEffect ::
    forall effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    )
    => ChainIndexEffect
    ~> Eff effs
handleChainIndexEffect = runChainIndexEffects . \case
    StartWatching a           -> WalletEffects.startWatching a
    WatchedAddresses          -> WalletEffects.watchedAddresses
    ConfirmedBlocks           -> WalletEffects.confirmedBlocks
    TransactionConfirmed txid -> WalletEffects.transactionConfirmed txid
    NextTx r                  -> WalletEffects.nextTx r

handleChainIndexControlEffect ::
    forall effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    )
    => ChainIndex.ChainIndexControlEffect
    ~> Eff effs
handleChainIndexControlEffect = runChainIndexEffects . \case
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
    forall effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (Reader InstancesState) effs
    , Member (Reader BlockchainEnv) effs
    , Member DelayEffect effs
    , Member TimeEffect effs
    )
    => Eff effs ()
advanceClock = forever makeBlock

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
    Contract.PutState def instanceId state -> do
        instancesTVar <- view instances <$> (Core.userEnv @t @(SimulatorState t))
        liftIO $ STM.atomically $ do
            let instState = SimulatorContractInstanceState{_contractDef = def, _contractState = state}
            STM.modifyTVar instancesTVar (set (at instanceId) (Just instState))
    Contract.GetState instanceId -> do
        instancesTVar <- view instances <$> (Core.userEnv @t @(SimulatorState t))
        result <- preview (at instanceId . _Just . contractState) <$> liftIO (STM.readTVarIO instancesTVar)
        case result of
            Just s  -> pure s
            Nothing -> throwError (ContractInstanceNotFound instanceId)
    Contract.ActiveContracts -> do
        instancesTVar <- view instances <$> (Core.userEnv @t @(SimulatorState t))
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
txCounts ::
    ( Member (Reader (SimulatorState TestContracts)) effs
    , LastMember IO effs
    )
    => Eff effs TxCounts
txCounts = do
    SimulatorState{_chainState} <- ask @(SimulatorState TestContracts)
    Chain.ChainState{Chain._chainNewestFirst, Chain._txPool} <- liftIO $ STM.readTVarIO _chainState
    return
        $ TxCounts
            { _txValidated = sum (length <$> _chainNewestFirst)
            , _txMemPool   = length _txPool
            }

-- | The set of all active contracts.
activeContracts :: Simulation (Set ContractInstanceId)
activeContracts = Core.activeContracts

-- | The total value currently at an address
valueAt ::
    ( Member (Reader (SimulatorState TestContracts)) effs
    , LastMember IO effs
    )
    => Address
    -> Eff effs Value
valueAt address = do
    SimulatorState{_chainState} <- ask @(SimulatorState TestContracts)
    Chain.ChainState{Chain._index=UtxoIndex.UtxoIndex mp} <- liftIO $ STM.readTVarIO _chainState
    pure $ foldMap txOutValue $ filter (\TxOut{txOutAddress} -> txOutAddress == address) $ fmap snd $ Map.toList mp

-- | The entire chain (newest transactions first)
blockchain ::
    ( Member (Reader (SimulatorState TestContracts)) effs
    , LastMember IO effs
    )
    => Eff effs [[Tx]]
blockchain = do
    SimulatorState{_chainState} <- ask @(SimulatorState TestContracts)
    Chain.ChainState{Chain._chainNewestFirst} <- liftIO $ STM.readTVarIO _chainState
    pure _chainNewestFirst
