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
    AgentThread
    , ControlThread
    , runAgentEffects
    , chainState
    , agentStates
    , chainIndex
    -- * Agents
    , AgentState(..)
    , initialAgentState
    -- Testing
    , test
    ) where

import           Control.Concurrent.STM                   (TVar)
import qualified Control.Concurrent.STM                   as STM
import           Control.Lens                             (Lens', makeLenses, view, (&), (.~))
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
import           Wallet.Emulator.MultiAgent               (EmulatorTimeEvent (..))
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

initialAgentState :: Wallet -> AgentState
initialAgentState wallet = AgentState{_walletState = Wallet.emptyWalletState wallet}

data SimulatorState =
    SimulatorState
        { _logMessages :: TVar [LogMessage PABMultiAgentMsg]
        , _currentSlot :: TVar Slot
        , _chainState  :: TVar ChainState
        , _agentStates :: TVar (Map Wallet AgentState)
        , _chainIndex  :: TVar ChainIndex.ChainIndexState
        }

makeLenses ''SimulatorState

initialState :: IO SimulatorState
initialState = STM.atomically $
    SimulatorState
        <$> STM.newTVar mempty
        <*> STM.newTVar 0
        <*> STM.newTVar Chain.emptyChainState
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

handleAgentThread ::
    forall a.
    SimulatorState
    -> Wallet
    -> Eff (AgentEffects '[IO]) a
    -> IO (Either PABError a)
handleAgentThread state wallet action = do
    let action' :: Eff (AgentEffects '[IO, Writer [LogMessage PABMultiAgentMsg], Error PABError, Reader SimulatorState, IO]) a = Modify.raiseEnd action
        makeTimedWalletEvent wllt =
            interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter _singleton)
            . reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog (WalletEvent wllt))
        makeTimedChainEvent =
            interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter _singleton)
            . reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog ChainEvent)
        makeTimedChainIndexEvent wllt =
            interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter _singleton)
            . reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog (ChainIndexEvent wllt))
    runM
        $ runReader state
        $ runError
        $ interpret (writeIntoStateTVar logMessages) -- TODO: We could also print it to the terminal
        $ subsume @IO
        $ subsume @(Error PABError)
        $ (makeTimedWalletEvent wallet . reinterpret (mapLog GenericLog))
        $ handleObserveLog
        $ interpret (handleLogWriter _InstanceMsg)
        $ (makeTimedWalletEvent wallet . reinterpret (mapLog RequestHandlerLog))
        $ (makeTimedWalletEvent wallet . reinterpret (mapLog TxBalanceLog))

        $ makeTimedChainEvent
        $ reinterpret @_ @(LogMsg Chain.ChainEvent) handleChainEffect

        $ interpret handleNodeClient

        $ makeTimedChainIndexEvent wallet
        $ reinterpret @_ @(LogMsg ChainIndex.ChainIndexEvent) handleChainIndexEffect

        $ flip (handleError @WAPI.WalletAPIError) (throwError @PABError . WalletError)
        $ interpret (runWalletState wallet)
        $ reinterpret2 @_ @(State Wallet.WalletState) @(Error WAPI.WalletAPIError) Wallet.handleWallet
        $ action'

runWalletState ::
    forall m effs.
    ( MonadIO m
    , LastMember m effs
    , Member (Reader SimulatorState) effs
    )
    => Wallet
    -> State Wallet.WalletState
    ~> Eff effs
runWalletState wallet = \case
    Get -> do
        SimulatorState{_agentStates} <- ask
        liftIO $ STM.atomically $ do
            mp <- STM.readTVar _agentStates
            case Map.lookup wallet mp of
                Nothing -> do
                    let newState = initialAgentState wallet
                    STM.writeTVar _agentStates (Map.insert wallet newState mp)
                    pure (_walletState newState)
                Just s -> pure (_walletState s)
    Put s -> do
        SimulatorState{_agentStates} <- ask
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
    AgentThread a
    -> Eff '[Reader SimulatorState, IO] (Either PABError a)
runAgentEffects action = do
    state <- ask
    result <- liftIO $ handleAgentThread state (Wallet 1) action
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
            interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter _singleton)
            . reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog (ChainIndexEvent (Wallet 0)))
    liftIO
        $ runM
        $ runReader state
        $ interpret (writeIntoStateTVar logMessages) -- TODO: We could also print it to the terminal
        $ subsume @IO
        $ makeTimedChainIndexEvent
        $ makeTimedChainEvent
        $ interpret handleChainIndexControlEffect
        $ interpret handleChainControl action'


test :: IO ()
test = do
    state <- initialState
    _ <- runM $ runReader state $ do
        _ <- runControlEffects Chain.processBlock
        _ <- runAgentEffects $ logInfo @(ContractInstanceMsg TestContracts) InboxMessageMatchesIteration
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
    => LogMsg e
    ~> Eff effs
timed = \case
    LMessage m -> do
        m' <- forM m $ \msg -> do
            sl <- asks (view currentSlot) >>= liftIO . STM.readTVarIO
            pure (EmulatorTimeEvent sl msg)
        send (LMessage m')

-- | Handle a 'Writer' effect in terms of a "larger" 'State' effect from which we have a setter.
writeIntoStateTVar ::
    forall s1 s2 m effs.
    ( Monoid s1
    , Member (Reader s2) effs
    , LastMember m effs
    , MonadIO m
    )
    => Lens' s2 (TVar s1)
    -> (Writer s1 ~> Eff effs)
writeIntoStateTVar s = \case
    Tell w -> do
        tv <- asks (view s)
        liftIO $ STM.atomically $ STM.modifyTVar tv (<> w)

handleChainControl ::
    forall m effs.
    ( MonadIO m
    , LastMember m effs
    , Member (Reader SimulatorState) effs
    , Member (LogMsg Chain.ChainEvent) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    )
    => ChainControlEffect
    ~> Eff effs
handleChainControl = \case
    Chain.ProcessBlock -> do
        (txns, slot) <- runChainEffects @_ @m $ do
                txns <- Chain.processBlock
                sl <- Chain.getCurrentSlot
                pure (txns, sl)
        runChainIndexEffects $ do
            ChainIndex.chainIndexNotify $ BlockValidated txns
            ChainIndex.chainIndexNotify $ SlotChanged slot
        pure txns

runChainEffects ::
    forall a m effs.
    ( Member (Reader SimulatorState) effs
    , Member (LogMsg Chain.ChainEvent) effs
    , LastMember m effs
    , MonadIO m
    )
    => Eff (Chain.ChainEffect ': Chain.ChainControlEffect ': Chain.ChainEffs) a
    -> Eff effs a
runChainEffects action = do
    SimulatorState{_chainState, _currentSlot} <- ask
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
    ( Member (Reader SimulatorState) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    , LastMember m effs
    , MonadIO m
    )
    => Eff (ChainIndexEffect ': ChainIndex.ChainIndexControlEffect ': ChainIndex.ChainIndexEffs) a
    -> Eff effs a
runChainIndexEffects action = do
    SimulatorState{_chainIndex} <- ask
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
    , Member (Reader SimulatorState) effs
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
    , Member (Reader SimulatorState) effs
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
    , Member (Reader SimulatorState) effs
    , Member (LogMsg ChainIndex.ChainIndexEvent) effs
    )
    => ChainIndex.ChainIndexControlEffect
    ~> Eff effs
handleChainIndexControlEffect = runChainIndexEffects . \case
    ChainIndex.ChainIndexNotify n -> ChainIndex.chainIndexNotify n

-- TODO: make activateContractSTM work
--       fix tests / app
--       implement new client API
