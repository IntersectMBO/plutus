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
    AgentThread
    , ControlThread
    , runAgentEffects
    , chainState
    , agentStates
    , chainIndex
    -- * Agents
    , AgentState(..)
    , initialAgentState
    , agentState
    -- Testing
    , test
    ) where

import           Control.Concurrent.STM                   (TVar)
import qualified Control.Concurrent.STM                   as STM
import           Control.Lens                             (Lens', anon, at, makeLenses, view, (&), (.~))
import           Control.Monad                            (forM, unless, void)
import           Control.Monad.Freer                      (Eff, LastMember, Member, interpret, reinterpret,
                                                           reinterpret2, run, runM, send, subsume, type (~>))
import           Control.Monad.Freer.Error                (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extras.Log           (LogMessage, LogMsg (..), LogObserve, handleLogWriter,
                                                           handleObserveLog, logInfo, mapLog)
import qualified Control.Monad.Freer.Extras.Modify        as Modify
import           Control.Monad.Freer.Reader               (Reader, ask, asks, runReader)
import           Control.Monad.Freer.State                (State (..), runState)
import           Control.Monad.Freer.Writer               (Writer (..), runWriter)
import           Control.Monad.IO.Class                   (MonadIO (..))
import           Data.Foldable                            (traverse_)
import           Data.Map                                 (Map)
import qualified Data.Map                                 as Map
import           Data.Text                                (Text)
import qualified Ledger.Ada                               as Ada
import qualified Wallet.Emulator                          as Emulator
import           Wallet.Emulator.MultiAgent               (EmulatorTimeEvent (..))
import qualified Wallet.Emulator.MultiAgent               as Emulator
import qualified Wallet.Emulator.Stream                   as Emulator
import           Wallet.Emulator.Wallet                   (Wallet (..), WalletEvent (..))

import           Plutus.PAB.Core.ContractInstance         as ContractInstance
import           Plutus.PAB.Effects.Contract.ContractTest (TestContracts (..))
import           Plutus.PAB.Effects.MultiAgent            (PABMultiAgentMsg (..), _InstanceMsg)
import           Plutus.PAB.Types                         (PABError (WalletError))
import           Plutus.V1.Ledger.Slot                    (Slot)
import qualified Wallet.API                               as WAPI
import           Wallet.Effects                           (ChainIndexEffect (..), NodeClientEffect (..), WalletEffect)
import qualified Wallet.Effects                           as WalletEffects
import           Wallet.Emulator.Chain                    (ChainControlEffect, ChainState)
import qualified Wallet.Emulator.Chain                    as Chain
import qualified Wallet.Emulator.ChainIndex               as ChainIndex
import           Wallet.Emulator.LogMessages              (RequestHandlerLogMsg, TxBalanceMsg)
import           Wallet.Emulator.MultiAgent               (EmulatorEvent' (..), _singleton)
import           Wallet.Emulator.NodeClient               (ChainClientNotification (..))
import qualified Wallet.Emulator.Wallet                   as Wallet

data AgentState =
    AgentState
        { _walletState :: Wallet.WalletState
        }

makeLenses ''AgentState

initialAgentState :: forall t. Wallet -> AgentState t
initialAgentState wallet =
    AgentState
        { _walletState = Wallet.emptyWalletState wallet
        }

agentState :: Wallet.Wallet -> Lens' (Map Wallet AgentState) AgentState
agentState wallet = at wallet . anon (initialAgentState wallet) (const False)

data SimulatorState =
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

initialState :: IO SimulatorState
initialState = do
    let Emulator.EmulatorState{Emulator._chainState} = Emulator.initialState Emulator.defaultEmulatorConfig
    STM.atomically $
        SimulatorState
            <$> STM.newTVar mempty
            <*> STM.newTVar 0
            <*> STM.newTVar _chainState
            <*> STM.newTVar mempty
            <*> STM.newTVar mempty

-- | Effects available to simulated agents that run in their own thread
    -- , Member WalletEffect effs
    -- , Member ContractRuntimeEffect effs
--   TODO: AppBackendConstraints for agent!
type AgentEffects effs =
    WalletEffect
    ': ChainIndexEffect
    ': NodeClientEffect
    ': Chain.ChainEffect
    ': LogMsg TxBalanceMsg
    ': LogMsg RequestHandlerLogMsg
    ': LogMsg (ContractInstanceMsg TestContracts)
    ': LogObserve (LogMessage Text)
    ': LogMsg Text
    ': Error PABError
    ': effs

type AgentThread a = Eff (AgentEffects '[IO]) a

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


runAgentEffects ::
    forall a.
    Wallet
    -> AgentThread a
    -> Eff '[Reader SimulatorState, IO] (Either PABError a)
runAgentEffects wallet action = do
    state <- ask
    result <- liftIO $ handleAgentThread state wallet action
    pure result

-- | Control effects for managing the chain
type ControlEffects effs =
    ChainControlEffect
    ': ChainIndex.ChainIndexControlEffect
    ': LogMsg Chain.ChainEvent
    ': LogMsg ChainIndex.ChainIndexEvent
    ': effs

type ControlThread a = Eff (ControlEffects '[IO]) a

runControlEffects ::
    forall a.
    ControlThread a
    -> Eff '[Reader SimulatorState, IO] a
runControlEffects action = do
    state <- ask
    let action' :: Eff (ControlEffects '[IO, Writer [LogMessage PABMultiAgentMsg], Reader SimulatorState, IO]) a = Modify.raiseEnd action
        makeTimedChainEvent =
            interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter _singleton)
            . reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
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
        $ interpret handleChainIndexControlEffect
        $ interpret handleChainControl action'


test :: IO ()
test = do
    state <- initialState
    _ <- runM $ runReader state $ do
        _ <- runControlEffects Chain.processBlock
        _ <- runAgentEffects (Wallet 1) $ logInfo @(ContractInstanceMsg TestContracts) InboxMessageMatchesIteration
        _ <- runAgentEffects (Wallet 1) $ WAPI.payToPublicKey WAPI.defaultSlotRange (Ada.adaValueOf 1) (Emulator.walletPubKey (Wallet 2))
        void $ runControlEffects Chain.processBlock
    let SimulatorState{_logMessages, _currentSlot} = state
    lms <- STM.atomically $ STM.readTVar _logMessages
    traverse_ print lms
    STM.atomically (STM.readTVar _currentSlot) >>= print

-- | Annotate log messages with the current slot number.
timed ::
    forall e m effs.
    ( Member (Reader SimulatorState) effs
    , Member (LogMsg (EmulatorTimeEvent e)) effs
    , LastMember m effs
    , MonadIO m
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

-- TODO: Delete MultiAgent, MockApp (all replaced by this module)
-- TODO: Maybe use InMemory eventful stuff?
-- TODO: Initial transaction
---      make activateContractSTM work
--       fix tests / app
--       implement new client API
