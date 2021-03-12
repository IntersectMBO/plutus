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

A multi-threaded PAB simulator

-}
module Plutus.PAB.Simulator(
    runSimulator
    -- * Simulator actions
    , logString
    , payToWallet
    , activateContract
    , callEndpointOnInstance
    -- * Types
    , AgentThread
    , ControlThread
    , runAgentEffects
    , chainState
    , agentStates
    , chainIndex
    -- * Agents
    , AgentState(..)
    , initialAgentState
    , agentState
    , instances
    -- * Contract instances
    , SimulatorContractInstanceState
    , contractState
    , contractDef

    -- Testing
    , test
    ) where

import           Control.Concurrent                                (forkIO)
import           Control.Concurrent.STM                            (TQueue, TVar)
import qualified Control.Concurrent.STM                            as STM
import           Control.Lens                                      (Lens', _Just, anon, at, makeLenses, preview, set,
                                                                    to, view, (&), (.~), (^.))
import           Control.Monad                                     (forM, forever, unless, void, when)
import           Control.Monad.Freer                               (Eff, LastMember, Member, interpret, reinterpret,
                                                                    reinterpret2, run, runM, send, subsume, type (~>))
import           Control.Monad.Freer.Delay                         (DelayEffect, delayThread, handleDelayEffect)
import           Control.Monad.Freer.Error                         (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extras.Log                    (LogLevel (Info), LogMessage, LogMsg (..),
                                                                    LogObserve, handleLogWriter, handleObserveLog,
                                                                    logInfo, logLevel, mapLog)
import qualified Control.Monad.Freer.Extras.Modify                 as Modify
import           Control.Monad.Freer.Reader                        (Reader, ask, asks, runReader)
import           Control.Monad.Freer.State                         (State (..), runState)
import           Control.Monad.Freer.Writer                        (Writer (..), runWriter)
import           Control.Monad.IO.Class                            (MonadIO (..))
import qualified Data.Aeson                                        as JSON
import           Data.Foldable                                     (traverse_)
import           Data.Map                                          (Map)
import qualified Data.Map                                          as Map
import           Data.Text                                         (Text)
import qualified Data.Text.IO                                      as Text
import           Data.Text.Prettyprint.Doc                         (Pretty (pretty), defaultLayoutOptions, layoutPretty)
import qualified Data.Text.Prettyprint.Doc.Render.Text             as Render
import           Data.Time.Units                                   (Millisecond)
import qualified Language.PlutusTx.Coordination.Contracts.Currency as Currency
import qualified Ledger.Ada                                        as Ada
import           Ledger.Tx                                         (Tx)
import           Ledger.Value                                      (Value)
import           Plutus.PAB.Effects.UUID                           (UUIDEffect, handleUUIDEffect)
import qualified Wallet.Emulator                                   as Emulator
import           Wallet.Emulator.MultiAgent                        (EmulatorTimeEvent (..))
import qualified Wallet.Emulator.Stream                            as Emulator
import           Wallet.Emulator.Wallet                            (Wallet (..), WalletEvent (..))

import qualified Plutus.PAB.Core.ContractInstance                  as ContractInstance
import qualified Plutus.PAB.Core.ContractInstance.BlockchainEnv    as BlockchainEnv
import           Plutus.PAB.Core.ContractInstance.STM              (BlockchainEnv, InstancesState)
import qualified Plutus.PAB.Core.ContractInstance.STM              as Instances
import           Plutus.PAB.Effects.Contract                       (ContractEffect, ContractStore)
import qualified Plutus.PAB.Effects.Contract                       as Contract
import           Plutus.PAB.Effects.Contract.ContractTest          (ContractTestMsg, TestContracts (..),
                                                                    handleContractTest)
import qualified Plutus.PAB.Effects.ContractRuntime                as ContractRuntime
import           Plutus.PAB.Effects.MultiAgent                     (PABMultiAgentMsg (..))
import           Plutus.PAB.Types                                  (PABError (ContractInstanceNotFound, WalletError))
import           Plutus.V1.Ledger.Slot                             (Slot)
import qualified Wallet.API                                        as WAPI
import           Wallet.Effects                                    (ChainIndexEffect (..), ContractRuntimeEffect,
                                                                    NodeClientEffect (..), WalletEffect)
import qualified Wallet.Effects                                    as WalletEffects
import           Wallet.Emulator.Chain                             (ChainControlEffect, ChainState)
import qualified Wallet.Emulator.Chain                             as Chain
import qualified Wallet.Emulator.ChainIndex                        as ChainIndex
import           Wallet.Emulator.LogMessages                       (RequestHandlerLogMsg, TxBalanceMsg)
import           Wallet.Emulator.MultiAgent                        (EmulatorEvent' (..), _singleton)
import           Wallet.Emulator.NodeClient                        (ChainClientNotification (..))
import qualified Wallet.Emulator.Wallet                            as Wallet
import           Wallet.Types                                      (ContractInstanceId, EndpointDescription (..),
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
        , _instances   :: Map ContractInstanceId (SimulatorContractInstanceState t)
        }

makeLenses ''AgentState

initialAgentState :: forall t. Wallet -> AgentState t
initialAgentState wallet =
    AgentState
        { _walletState = Wallet.emptyWalletState wallet
        , _instances   = Map.empty
        }

agentState :: forall t. Wallet.Wallet -> Lens' (Map Wallet (AgentState t)) (AgentState t)
agentState wallet = at wallet . anon (initialAgentState wallet) (const False)

data SimulatorState t =
    SimulatorState
        { _logMessages :: TQueue (LogMessage PABMultiAgentMsg)
        , _currentSlot :: TVar Slot
        , _chainState  :: TVar ChainState
        , _agentStates :: TVar (Map Wallet (AgentState t))
        , _chainIndex  :: TVar ChainIndex.ChainIndexState
        }

makeLenses ''SimulatorState

initialState :: forall t. IO (SimulatorState t)
initialState = do
    let Emulator.EmulatorState{Emulator._chainState} = Emulator.initialState Emulator.defaultEmulatorConfig
    STM.atomically $
        SimulatorState
            <$> STM.newTQueue
            <*> STM.newTVar 0
            <*> STM.newTVar _chainState
            <*> STM.newTVar mempty
            <*> STM.newTVar mempty

-- | Effects available to simulated agents that run in their own thread
    -- , Member ContractRuntimeEffect effs
--   TODO: AppBackendConstraints for agent!
type AgentEffects effs =
    ContractRuntimeEffect
    ': ContractEffect TestContracts
    ': ContractStore TestContracts
    ': WalletEffect
    ': ChainIndexEffect
    ': NodeClientEffect
    ': Chain.ChainEffect
    ': UUIDEffect
    ': LogMsg TxBalanceMsg
    ': LogMsg RequestHandlerLogMsg
    ': LogMsg (ContractInstance.ContractInstanceMsg TestContracts)
    ': LogObserve (LogMessage Text)
    ': LogMsg Text
    ': Error PABError
    ': Reader InstancesState
    ': Reader BlockchainEnv
    ': Reader Wallet
    ': Reader (SimulatorState TestContracts)
    ': effs

type AgentThread a = Eff (AgentEffects '[IO]) a

handleAgentThread ::
    forall a.
    SimulatorState TestContracts
    -> BlockchainEnv
    -> InstancesState
    -> Wallet
    -> Eff (AgentEffects '[IO]) a
    -> IO (Either PABError a)
handleAgentThread state blockchainEnv instancesState wallet action = do
    let action' :: Eff (AgentEffects '[IO, LogMsg PABMultiAgentMsg, Error PABError, Reader (SimulatorState TestContracts), IO]) a = Modify.raiseEnd action
        makeTimedWalletEvent wllt =
            interpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog (WalletEvent wllt))
        makeTimedChainEvent =
            interpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog ChainEvent)
        makeTimedChainIndexEvent wllt =
            interpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog (ChainIndexEvent wllt))

        handleContractTestMsg :: forall x effs. Member (LogMsg PABMultiAgentMsg) effs => Eff (LogMsg ContractTestMsg ': effs) x -> Eff effs x
        handleContractTestMsg = interpret (mapLog @_ @PABMultiAgentMsg ContractMsg)

        handleContractRuntimeMsg :: forall x effs. Member (LogMsg PABMultiAgentMsg) effs => Eff (LogMsg ContractRuntime.ContractRuntimeMsg ': effs) x -> Eff effs x
        handleContractRuntimeMsg = interpret (mapLog @_ @PABMultiAgentMsg RuntimeLog)
    runM
        $ runReader state
        $ runError
        $ interpret (writeIntoTQueue @_ @(SimulatorState TestContracts) logMessages)
        $ reinterpret @(LogMsg PABMultiAgentMsg) @(Writer (LogMessage PABMultiAgentMsg)) (handleLogWriter id)  -- TODO: We could also print it to the terminal
        $ subsume @IO
        $ subsume @(Reader (SimulatorState TestContracts))
        $ runReader wallet
        $ runReader blockchainEnv
        $ runReader instancesState
        $ subsume @(Error PABError)
        $ (makeTimedWalletEvent wallet . reinterpret (mapLog GenericLog))
        $ handleObserveLog
        $ interpret (mapLog ContractInstanceLog)
        $ (makeTimedWalletEvent wallet . reinterpret (mapLog RequestHandlerLog))
        $ (makeTimedWalletEvent wallet . reinterpret (mapLog TxBalanceLog))

        $ handleUUIDEffect

        $ makeTimedChainEvent
        $ reinterpret @_ @(LogMsg Chain.ChainEvent) handleChainEffect

        $ interpret handleNodeClient

        $ makeTimedChainIndexEvent wallet
        $ reinterpret @_ @(LogMsg ChainIndex.ChainIndexEvent) handleChainIndexEffect

        $ flip (handleError @WAPI.WalletAPIError) (throwError @PABError . WalletError)
        $ interpret (runWalletState wallet)
        $ reinterpret2 @_ @(State Wallet.WalletState) @(Error WAPI.WalletAPIError) Wallet.handleWallet

        $ interpret @(ContractStore TestContracts) (handleContractStore wallet)

        $ handleContractTestMsg
        $ reinterpret @(ContractEffect TestContracts) @(LogMsg ContractTestMsg) handleContractTest

        $ handleContractRuntimeMsg
        $ reinterpret @ContractRuntimeEffect @(LogMsg ContractRuntime.ContractRuntimeMsg) (ContractRuntime.handleContractRuntime @TestContracts)

        $ action'

runWalletState ::
    forall m effs.
    ( MonadIO m
    , LastMember m effs
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


runAgentEffects ::
    forall a effs.
    ( Member (Reader InstancesState) effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (Reader BlockchainEnv) effs
    , LastMember IO effs
    )
    => Wallet
    -> AgentThread a
    -> Eff effs (Either PABError a)
runAgentEffects wallet action = do
    state <- ask @(SimulatorState TestContracts)
    inst <- ask @InstancesState
    blockchainEnv <- ask @BlockchainEnv
    result <- liftIO $ handleAgentThread state blockchainEnv inst wallet action
    pure result

-- | Control effects for managing the chain
type ControlEffects effs =
    ChainControlEffect
    ': ChainIndex.ChainIndexControlEffect
    ': LogMsg Chain.ChainEvent
    ': LogMsg ChainIndex.ChainIndexEvent
    ': Reader InstancesState
    ': Reader BlockchainEnv
    ': effs

type ControlThread a = Eff (ControlEffects '[IO]) a

runControlEffects ::
    forall a effs.
    ( Member (Reader InstancesState) effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (Reader BlockchainEnv) effs
    , LastMember IO effs
    )
    => ControlThread a
    -> Eff effs a
runControlEffects action = do
    state <- ask @(SimulatorState TestContracts)
    instancesState <- ask @InstancesState
    blockchainEnv <- ask @BlockchainEnv
    let action' :: Eff (ControlEffects '[IO, Writer (LogMessage PABMultiAgentMsg), Reader (SimulatorState TestContracts), IO]) a = Modify.raiseEnd action
        makeTimedChainEvent =
            interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter id)
            . reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog ChainEvent)
        makeTimedChainIndexEvent =
            interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter id)
            . reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog (ChainIndexEvent (Wallet 0)))
    liftIO
        $ runM
        $ runReader state
        $ interpret (writeIntoTQueue @_ @(SimulatorState TestContracts) logMessages)
        $ subsume @IO
        $ runReader blockchainEnv
        $ runReader instancesState
        $ makeTimedChainIndexEvent
        $ makeTimedChainEvent
        $ interpret handleChainIndexControlEffect
        $ interpret handleChainControl action'

-- | Make a payment to a wallet
payToWallet :: Member WalletEffect effs => Wallet -> Value -> Eff effs Tx
payToWallet target amount = WAPI.payToPublicKey WAPI.defaultSlotRange amount (Emulator.walletPubKey target)

-- | Start a new instance of a contract
activateContract ::
    forall effs.
    ( Member (LogMsg (ContractInstance.ContractInstanceMsg TestContracts)) effs
    , Member (ContractEffect TestContracts) effs
    , Member (ContractStore TestContracts) effs
    , Member (Reader Wallet) effs
    , Member (Reader InstancesState) effs
    , Member (Reader BlockchainEnv) effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , LastMember IO effs
    , Member UUIDEffect effs
    )
    => TestContracts
    -> Eff effs ContractInstanceId
activateContract def = do
    w <- ask @Wallet
    blockchainEnv <- ask @BlockchainEnv
    instancesState <- ask @InstancesState
    simState <- ask @(SimulatorState TestContracts)
    let handler :: forall a. Eff (AgentEffects '[IO]) a -> IO a
        handler x = fmap (either (error . show) id) (handleAgentThread simState blockchainEnv instancesState w x)
    ContractInstance.activateContractSTM @TestContracts @IO @(AgentEffects '[IO]) handler def

-- | Call a named endpoint on a contract instance
callEndpointOnInstance ::
    forall a effs.
    ( Member (Reader InstancesState) effs
    , JSON.ToJSON a
    , LastMember IO effs
    )
    => ContractInstanceId
    -> String
    -> a
    -> Eff effs (Maybe NotificationError)
callEndpointOnInstance instanceID ep value = do
    state <- ask @InstancesState
    liftIO $ STM.atomically $ Instances.callEndpointOnInstance state (EndpointDescription ep) (JSON.toJSON value) instanceID

-- | Log some output to the console
logString :: Member (LogMsg PABMultiAgentMsg) effs => String -> Eff effs ()
logString = logInfo . UserLog

nextSlot ::
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (Reader InstancesState) effs
    , Member (Reader BlockchainEnv) effs
    , Member DelayEffect effs
    ) => Eff effs ()
nextSlot = do
    delayThread (500 :: Millisecond)
    void $ runControlEffects Chain.processBlock

-- | Run a simulation on a mockchain with initial values
runSimulator ::
    Eff '[LogMsg PABMultiAgentMsg, Reader (SimulatorState TestContracts), Reader InstancesState, Reader BlockchainEnv, DelayEffect, IO] a
    -> IO (SimulatorState TestContracts, a)
runSimulator action = do
    state <- initialState
    inst <- STM.atomically Instances.emptyInstancesState
    blockchainEnv <- STM.atomically Instances.emptyBlockchainEnv
    printLogMessages (_logMessages state)
    a <- runM
            $ handleDelayEffect
            $ runReader blockchainEnv
            $ runReader inst
            $ runReader state
            $ interpret (writeIntoTQueue @_ @(SimulatorState TestContracts) logMessages)
            $ reinterpret @(LogMsg PABMultiAgentMsg) (handleLogWriter id)
            $ do
            -- Make 1st block with initial transaction
            _ <- runControlEffects Chain.processBlock
            action
    pure (state, a)

test :: IO ()
test = void $ runSimulator $ do
        _ <- runAgentEffects (Wallet 1) $ payToWallet (Wallet 2) (Ada.adaValueOf 1)
        nextSlot
        instanceID <- runAgentEffects (Wallet 1) $ activateContract Currency
        nextSlot
        result <- callEndpointOnInstance (either (error . show) id instanceID) "Create native token" (Currency.SimpleMPS{Currency.tokenName = "my token", Currency.amount = 1000})
        logString (show result)
        nextSlot
        nextSlot
        nextSlot

-- | Annotate log messages with the current slot number.
timed ::
    forall e m effs.
    ( Member (Reader (SimulatorState TestContracts)) effs
    , Member (LogMsg (EmulatorTimeEvent e)) effs
    , LastMember m effs
    , MonadIO m
    )
    => LogMsg e
    ~> Eff effs
timed = \case
    LMessage m -> do
        m' <- forM m $ \msg -> do
            sl <- asks @(SimulatorState TestContracts) (view currentSlot) >>= liftIO . STM.readTVarIO
            pure (EmulatorTimeEvent sl msg)
        send (LMessage m')

-- | Handle a 'Writer' effect in terms of a "larger" 'State' effect from which we have a setter.
writeIntoTQueue ::
    forall s1 s2 m effs.
    ( Member (Reader s2) effs
    , LastMember m effs
    , MonadIO m
    )
    => Lens' s2 (TQueue s1)
    -> (Writer s1 ~> Eff effs)
writeIntoTQueue s = \case
    Tell w -> do
        tv <- asks (view s)
        liftIO $ STM.atomically $ STM.writeTQueue tv w

handleChainControl ::
    forall m effs.
    ( MonadIO m
    , LastMember m effs
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
        (txns, slot) <- runChainEffects @_ @m $ do
                txns <- Chain.processBlock
                sl <- Chain.getCurrentSlot
                pure (txns, sl)
        runChainIndexEffects $ do
            ChainIndex.chainIndexNotify $ BlockValidated txns
            ChainIndex.chainIndexNotify $ SlotChanged slot
        liftIO $ STM.atomically $ BlockchainEnv.processBlock blockchainEnv instancesState txns slot
        pure txns

runChainEffects ::
    forall a m effs.
    ( Member (Reader (SimulatorState TestContracts)) effs
    , Member (LogMsg Chain.ChainEvent) effs
    , LastMember m effs
    , MonadIO m
    )
    => Eff (Chain.ChainEffect ': Chain.ChainControlEffect ': Chain.ChainEffs) a
    -> Eff effs a
runChainEffects action = do
    SimulatorState{_chainState, _currentSlot} <- ask @(SimulatorState TestContracts)
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
                            newSlot = view Chain.currentSlot newState
                        oldSlot <- STM.readTVar _currentSlot
                        unless (newSlot == oldSlot) $  STM.writeTVar _currentSlot newSlot
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


handleNodeClient ::
    forall effs.
    ( Member Chain.ChainEffect effs
    )
    => NodeClientEffect
    ~> Eff effs
handleNodeClient = \case
    PublishTx tx  -> Chain.queueTx tx
    GetClientSlot -> Chain.getCurrentSlot

handleChainEffect ::
    forall m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (LogMsg Chain.ChainEvent) effs
    )
    => Chain.ChainEffect
    ~> Eff effs
handleChainEffect = \case
    Chain.QueueTx tx     -> runChainEffects $ Chain.queueTx tx
    Chain.GetCurrentSlot -> runChainEffects $ Chain.getCurrentSlot

handleChainIndexEffect ::
    forall m effs.
    ( LastMember m effs
    , MonadIO m
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
    forall m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    )
    => ChainIndex.ChainIndexControlEffect
    ~> Eff effs
handleChainIndexControlEffect = runChainIndexEffects . \case
    ChainIndex.ChainIndexNotify n -> ChainIndex.chainIndexNotify n

-- TODO: Delete MultiAgent, MockApp (all replaced by this module)
-- TODO: Call endpoint
--       fix tests / app
--       implement new client API

-- | Start a thread that prints log messages to the terminal when they come in.
printLogMessages ::
    forall t.
    Pretty t
    => TQueue (LogMessage t)
    -> IO ()
printLogMessages queue = void $ forkIO $ forever $ do
    msg <- STM.atomically $ STM.readTQueue queue
    when (msg ^. logLevel >= Info) $ do
        let t = Render.renderStrict $ layoutPretty defaultLayoutOptions $ pretty msg
        Text.putStrLn t

handleContractStore ::
    forall t m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Reader (SimulatorState t)) effs
    , Member (Error PABError) effs
    )
    => Wallet
    -> ContractStore t
    ~> Eff effs
handleContractStore wallet = \case
    Contract.PutState def instanceId state -> do
        agentStatesTVar <- asks @(SimulatorState t) (view agentStates)
        liftIO $ STM.atomically $ do
            let instState = SimulatorContractInstanceState{_contractDef = def, _contractState = state}
            STM.modifyTVar agentStatesTVar (set (agentState wallet . instances . at instanceId) (Just instState))
    Contract.GetState instanceId -> do
        agentStatesTVar <- asks @(SimulatorState t) (view agentStates)
        result <- preview (agentState wallet . instances . at instanceId . _Just . contractState) <$> liftIO (STM.readTVarIO agentStatesTVar)
        case result of
            Just s  -> pure s
            Nothing -> throwError (ContractInstanceNotFound instanceId)
    Contract.ActiveContracts -> do
        agentStatesTVar <- asks @(SimulatorState t) (view agentStates)
        view (agentState wallet . instances . to (fmap _contractDef)) <$> liftIO (STM.readTVarIO agentStatesTVar)

-- TODO: Inspect instance state

-- valueAt :: Member (State TestState) effs => Address -> Eff effs Ledger.Value
-- blockchainNewestFirst :: Lens' TestState Blockchain

-- | Statistics about the transactions that have been validated by the emulated node.
-- data TxCounts =
--     TxCounts
--         { _txValidated :: Int
--         -- ^ How many transactions were checked and added to the ledger
--         , _txMemPool   :: Int
--         -- ^ How many transactions remain in the mempool of the emulated node
--         } deriving (Eq, Ord, Show)

-- txCounts :: Member (State TestState) effs => Eff effs TxCounts
-- txCounts = do
--     chain <- use blockchainNewestFirst
--     pool <- use (nodeState . NodeServer.chainState . Wallet.Emulator.Chain.txPool)
--     return
--         $ TxCounts
--             { _txValidated = lengthOf folded chain
--             , _txMemPool   = length pool
--             }
