{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
{-

A multi-threaded PAB simulator

-}
module Plutus.PAB.Simulator(
    AgentThread
    , ControlThread
    , runAgentEffects
    , chainState
    , test
    ) where

import           Control.Concurrent.STM                   (TVar)
import qualified Control.Concurrent.STM                   as STM
import           Control.Lens                             (Lens', makeLenses, view)
import           Control.Monad                            (forM, void)
import           Control.Monad.Freer                      (Eff, LastMember, Member, interpret, reinterpret, run, runM,
                                                           send, subsume, type (~>))
import           Control.Monad.Freer.Error                (Error, runError)
import           Control.Monad.Freer.Extras.Log           (LogMessage, LogMsg (..), LogObserve, handleLogWriter,
                                                           handleObserveLog, logInfo, mapLog)
import           Control.Monad.Freer.Extras.Modify        (raiseEnd3, raiseEnd7)
import           Control.Monad.Freer.Reader               (Reader, ask, asks, runReader)
import           Control.Monad.Freer.State                (runState)
import           Control.Monad.Freer.Writer               (Writer (..), runWriter)
import           Control.Monad.IO.Class                   (MonadIO (..))
import           Data.Foldable                            (traverse_)
import           Data.Text                                (Text)
import           Wallet.Emulator.MultiAgent               (EmulatorTimeEvent (..))
import           Wallet.Emulator.Wallet                   (Wallet (..), WalletEvent (..))

import           Plutus.PAB.Core.ContractInstance         as ContractInstance
import           Plutus.PAB.Effects.Contract.ContractTest (TestContracts (..))
import           Plutus.PAB.Effects.MultiAgent            (PABMultiAgentMsg (..), _InstanceMsg)
import           Plutus.PAB.Types                         (PABError)
import           Plutus.V1.Ledger.Slot                    (Slot)
import           Wallet.Emulator.Chain                    (ChainControlEffect, ChainState)
import qualified Wallet.Emulator.Chain                    as Chain
import           Wallet.Emulator.LogMessages              (RequestHandlerLogMsg, TxBalanceMsg)
import           Wallet.Emulator.MultiAgent               (EmulatorEvent' (..), _singleton)

data SimulatorState =
    SimulatorState
        { _logMessages :: TVar [LogMessage PABMultiAgentMsg]
        , _currentSlot :: TVar Slot
        , _chainState  :: TVar ChainState
        }

makeLenses ''SimulatorState

initialState :: IO SimulatorState
initialState = STM.atomically $
    SimulatorState
        <$> STM.newTVar mempty
        <*> STM.newTVar 0
        <*> STM.newTVar Chain.emptyChainState

-- | Effects available to simulated agents that run in their own thread
--   TODO: AppBackendConstraints for agent!
type AgentEffects effs =
    LogMsg TxBalanceMsg
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
    let action' :: Eff (AgentEffects '[IO, Writer [LogMessage PABMultiAgentMsg], Error PABError, Reader SimulatorState, IO]) a = raiseEnd7 action
        makeTimedWalletEvent wllt =
            interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter _singleton)
            . reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog (WalletEvent wllt))
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
        $ action'

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
    ': LogMsg Chain.ChainEvent
    ': effs

type ControlThread a = Eff (ControlEffects '[IO]) a

runControlEffects ::
    forall a.
    ControlThread a
    -> Eff '[Reader SimulatorState, IO] a
runControlEffects action = do
    state <- ask
    let action' :: Eff (ControlEffects '[IO, Writer [LogMessage PABMultiAgentMsg], Reader SimulatorState, IO]) a = raiseEnd3 action
        makeTimedChainEvent =
            interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter _singleton)
            . reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog ChainEvent)
    liftIO
        $ runM
        $ runReader state
        $ interpret (writeIntoStateTVar logMessages) -- TODO: We could also print it to the terminal
        $ subsume @IO
        $ makeTimedChainEvent
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
    )
    => ChainControlEffect
    ~> Eff effs
handleChainControl = \case
    Chain.ProcessBlock -> do
        SimulatorState{_chainState, _currentSlot} <- ask
        (txns, logs) <- liftIO $ STM.atomically $ do
                            oldState <- STM.readTVar _chainState
                            let ((txns, logs), newState) =
                                    run
                                    $ runState oldState
                                    $ runWriter @[LogMessage Chain.ChainEvent]
                                    $ interpret @(LogMsg Chain.ChainEvent) (handleLogWriter _singleton)
                                    $ interpret Chain.handleControlChain
                                    $ Chain.processBlock
                                newSlot = view Chain.currentSlot newState
                            STM.writeTVar _currentSlot newSlot
                            STM.writeTVar _chainState newState
                            pure (txns, logs)
        traverse_ (send . LMessage) logs
        pure txns


-- TODO
-- 1. Make timed emulator event
-- 2. Handler for node client effect
