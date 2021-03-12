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
    , agentAction
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
    , AgentThread
    , ControlThread
    , runAgentEffects
    , SimulatorState(..)
    , chainState
    , agentStates
    , chainIndex
    , instances
    , contractDef
    -- * Agents
    , AgentState(..)
    , initialAgentState
    , agentState
    -- * Runnning simulations
    , SimRunner(..)
    , mkRunSim
    ) where

import           Control.Applicative                             (Alternative (..))
import           Control.Concurrent                              (forkIO)
import           Control.Concurrent.STM                          (STM, TQueue, TVar)
import qualified Control.Concurrent.STM                          as STM
import           Control.Lens                                    (Lens', _Just, anon, at, makeLenses, preview, set,
                                                                  view, (&), (.~), (^.))
import           Control.Monad                                   (forM, forever, guard, void, when)
import           Control.Monad.Freer                             (Eff, LastMember, Member, interpret, reinterpret,
                                                                  reinterpret2, run, runM, send, subsume, type (~>))
import           Control.Monad.Freer.Delay                       (DelayEffect, delayThread, handleDelayEffect)
import           Control.Monad.Freer.Error                       (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extras.Log                  (LogLevel (Info), LogMessage, LogMsg (..), LogObserve,
                                                                  handleLogWriter, handleObserveLog, logInfo, logLevel,
                                                                  mapLog)
import qualified Control.Monad.Freer.Extras.Modify               as Modify
import           Control.Monad.Freer.Reader                      (Reader, ask, asks, runReader)
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
import qualified Ledger.Index                                    as UtxoIndex
import           Ledger.Tx                                       (Address, Tx, TxOut (..))
import           Ledger.Value                                    (Value)
import           Plutus.PAB.Effects.UUID                         (UUIDEffect, handleUUIDEffect)
import qualified Wallet.Emulator                                 as Emulator
import           Wallet.Emulator.MultiAgent                      (EmulatorTimeEvent (..))
import qualified Wallet.Emulator.Stream                          as Emulator
import           Wallet.Emulator.Wallet                          (Wallet (..), WalletEvent (..))

import           Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint (..))
import qualified Plutus.PAB.Core.ContractInstance                as ContractInstance
import qualified Plutus.PAB.Core.ContractInstance.BlockchainEnv  as BlockchainEnv
import           Plutus.PAB.Core.ContractInstance.STM            (BlockchainEnv, InstancesState, OpenEndpoint)
import qualified Plutus.PAB.Core.ContractInstance.STM            as Instances
import           Plutus.PAB.Effects.Contract                     (ContractEffect, ContractStore)
import qualified Plutus.PAB.Effects.Contract                     as Contract
import           Plutus.PAB.Effects.Contract.ContractTest        (ContractTestMsg, TestContracts (..),
                                                                  handleContractTest)
import qualified Plutus.PAB.Effects.ContractRuntime              as ContractRuntime
import           Plutus.PAB.Effects.MultiAgent                   (PABMultiAgentMsg (..))
import           Plutus.PAB.Types                                (PABError (ContractInstanceNotFound, WalletError))
import           Plutus.V1.Ledger.Slot                           (Slot)
import qualified Wallet.API                                      as WAPI
import           Wallet.Effects                                  (ChainIndexEffect (..), ContractRuntimeEffect,
                                                                  NodeClientEffect (..), WalletEffect)
import qualified Wallet.Effects                                  as WalletEffects
import           Wallet.Emulator.Chain                           (ChainControlEffect, ChainState)
import qualified Wallet.Emulator.Chain                           as Chain
import qualified Wallet.Emulator.ChainIndex                      as ChainIndex
import           Wallet.Emulator.LogMessages                     (RequestHandlerLogMsg, TxBalanceMsg)
import           Wallet.Emulator.MultiAgent                      (EmulatorEvent' (..), _singleton)
import           Wallet.Emulator.NodeClient                      (ChainClientNotification (..))
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

agentState :: forall t. Wallet.Wallet -> Lens' (Map Wallet (AgentState t)) (AgentState t)
agentState wallet = at wallet . anon (initialAgentState wallet) (const False)

data SimulatorState t =
    SimulatorState
        { _logMessages :: TQueue (LogMessage PABMultiAgentMsg)
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

-- | Effects available to simulated agents that run in their own thread
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

handleContractTestMsg :: forall x effs. Member (LogMsg PABMultiAgentMsg) effs => Eff (LogMsg ContractTestMsg ': effs) x -> Eff effs x
handleContractTestMsg = interpret (mapLog @_ @PABMultiAgentMsg ContractMsg)

handleContractRuntimeMsg :: forall x effs. Member (LogMsg PABMultiAgentMsg) effs => Eff (LogMsg ContractRuntime.ContractRuntimeMsg ': effs) x -> Eff effs x
handleContractRuntimeMsg = interpret (mapLog @_ @PABMultiAgentMsg RuntimeLog)

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

        $ interpret @(ContractStore TestContracts) handleContractStore

        $ handleContractTestMsg
        $ reinterpret @(ContractEffect TestContracts) @(LogMsg ContractTestMsg) handleContractTest

        $ handleContractRuntimeMsg
        $ reinterpret @ContractRuntimeEffect @(LogMsg ContractRuntime.ContractRuntimeMsg) ContractRuntime.handleContractRuntime

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

agentAction ::
    forall a effs.
    ( Member (Reader InstancesState) effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (Reader BlockchainEnv) effs
    , LastMember IO effs
    , Member (Error PABError) effs
    )
    => Wallet
    -> AgentThread a
    -> Eff effs a
agentAction wallet action = runAgentEffects wallet action >>= either throwError pure


-- | Control effects for managing the chain
type ControlEffects effs =
    ChainControlEffect
    ': ChainIndex.ChainIndexControlEffect
    ': LogMsg Chain.ChainEvent
    ': LogMsg ChainIndex.ChainIndexEvent
    ': LogMsg PABMultiAgentMsg
    ': Reader InstancesState
    ': Reader BlockchainEnv
    ': Reader (SimulatorState TestContracts)
    ': DelayEffect
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
        $ handleDelayEffect
        $ runReader state
        $ runReader blockchainEnv
        $ runReader instancesState
        $ interpret (handleLogWriter id)
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
logString = logInfo . UserLog . Text.pack

-- | Pretty-prin a value to the console
logPretty :: forall a effs. (Pretty a, Member (LogMsg PABMultiAgentMsg) effs) => a -> Eff effs ()
logPretty = logInfo . UserLog . render

-- | Wait 0.2 seconds, then add a new block.
makeBlock ::
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (Reader InstancesState) effs
    , Member (Reader BlockchainEnv) effs
    , Member DelayEffect effs
    ) => Eff effs ()
makeBlock = do
    delayThread (200 :: Millisecond)
    void $ runControlEffects Chain.processBlock

-- | Get the current state of the contract instance.
instanceState ::
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (Reader InstancesState) effs
    , Member (Reader BlockchainEnv) effs
    )
    => Wallet
    -> ContractInstanceId
    -> Eff effs (Either PABError (Contract.State TestContracts))
instanceState wallet instanceId =
    runAgentEffects wallet (Contract.getState @TestContracts instanceId)

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

type SimulatorEffects =
    '[ ContractStore TestContracts
     , ContractEffect TestContracts
     , LogMsg PABMultiAgentMsg
     , Reader (SimulatorState TestContracts)
     , Reader InstancesState
     , Reader BlockchainEnv
     , DelayEffect
     , Error PABError
     , IO
     ]

type Simulation a = Eff SimulatorEffects a

-- | Simulation running function
newtype SimRunner = SimRunner { runSim :: forall a. Simulation a -> IO (Either PABError a)}

-- | Use the environment of the simulation to build
--   a simulation running function.
mkRunSim :: Simulation SimRunner
mkRunSim = do
    simState <- ask @(SimulatorState TestContracts)
    instancesState <- ask @InstancesState
    blockchainEnv <- ask @BlockchainEnv
    pure $ SimRunner $ \action -> do
        runM
            $ runError
            $ handleDelayEffect
            $ runReader blockchainEnv
            $ runReader instancesState
            $ runReader simState
            $ interpret (writeIntoTQueue @_ @(SimulatorState TestContracts) logMessages)
            $ reinterpret @(LogMsg PABMultiAgentMsg) (handleLogWriter id)
            $ handleContractTestMsg
            $ reinterpret @_ @(LogMsg ContractTestMsg) handleContractTest
            $ interpret handleContractStore
            $ action

-- | Run a simulation on a mockchain with initial values
runSimulation ::
    Simulation a
    -> IO (Either PABError a)
runSimulation action = do
    state <- initialState
    inst <- STM.atomically Instances.emptyInstancesState
    blockchainEnv <- STM.atomically Instances.emptyBlockchainEnv
    -- TODO: Optionally start the webserver?

    printLogMessages (_logMessages state)

    a <- runM
            $ runError
            $ handleDelayEffect
            $ runReader blockchainEnv
            $ runReader inst
            $ runReader state
            $ interpret (writeIntoTQueue @_ @(SimulatorState TestContracts) logMessages)
            $ reinterpret @(LogMsg PABMultiAgentMsg) (handleLogWriter id)
            $ handleContractTestMsg
            $ reinterpret @_ @(LogMsg ContractTestMsg) handleContractTest
            $ interpret handleContractStore
            $ do
            void $ liftIO $ forkIO $ runM $ runReader state $ runReader inst $ runReader blockchainEnv $ handleDelayEffect $ advanceClock
            waitUntilSlot 1
            result <- action
            delayThread (500 :: Millisecond) -- need to wait a little to avoid garbled terminal output in GHCi.
            pure result
    pure a

-- | Annotate log messages with the current slot number.
timed ::
    forall e m effs.
    ( Member (LogMsg (EmulatorTimeEvent e)) effs
    , Member (Reader BlockchainEnv) effs
    , LastMember m effs
    , MonadIO m
    )
    => LogMsg e
    ~> Eff effs
timed = \case
    LMessage m -> do
        m' <- forM m $ \msg -> do
            sl <- asks @Instances.BlockchainEnv Instances.beCurrentSlot >>= liftIO . STM.readTVarIO
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

        void $ liftIO $ STM.atomically $ do
            cenv <- BlockchainEnv.getClientEnv instancesState
            BlockchainEnv.updateInterestingAddresses blockchainEnv cenv
            BlockchainEnv.processBlock blockchainEnv txns slot

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

-- | Start a thread that prints log messages to the terminal when they come in.
printLogMessages ::
    forall t.
    Pretty t
    => TQueue (LogMessage t) -- ^ log messages
    -> IO ()
printLogMessages queue = void $ forkIO $ forever $ do
    msg <- STM.atomically $ STM.readTQueue queue
    when (msg ^. logLevel >= Info) (Text.putStrLn (render msg))

advanceClock ::
    forall effs.
    ( LastMember IO effs
    , Member (Reader (SimulatorState TestContracts)) effs
    , Member (Reader InstancesState) effs
    , Member (Reader BlockchainEnv) effs
    , Member DelayEffect effs
    )
    => Eff effs ()
advanceClock = forever makeBlock

-- | Handle the 'ContractStore' effect by writing the state to the
--   TVar in 'SimulatorState'
handleContractStore ::
    forall t m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Reader (SimulatorState t)) effs
    , Member (Error PABError) effs
    )
    => ContractStore t
    ~> Eff effs
handleContractStore = \case
    Contract.PutState def instanceId state -> do
        instancesTVar <- asks @(SimulatorState t) (view instances)
        liftIO $ STM.atomically $ do
            let instState = SimulatorContractInstanceState{_contractDef = def, _contractState = state}
            STM.modifyTVar instancesTVar (set (at instanceId) (Just instState))
    Contract.GetState instanceId -> do
        instancesTVar <- asks @(SimulatorState t) (view instances)
        result <- preview (at instanceId . _Just . contractState) <$> liftIO (STM.readTVarIO instancesTVar)
        case result of
            Just s  -> pure s
            Nothing -> throwError (ContractInstanceNotFound instanceId)
    Contract.ActiveContracts -> do
        instancesTVar <- asks @(SimulatorState t) (view instances)
        fmap _contractDef <$> liftIO (STM.readTVarIO instancesTVar)

render :: forall a. Pretty a => a -> Text
render = Render.renderStrict . layoutPretty defaultLayoutOptions . pretty


-- | Statistics about the transactions that have been validated by the emulated node.
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

activeContracts ::
    ( Member (Reader InstancesState) effs
    , LastMember IO effs
    )
    => Eff effs (Set ContractInstanceId)
activeContracts = ask >>= liftIO . STM.atomically . Instances.instanceIDs

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
