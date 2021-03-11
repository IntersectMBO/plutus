{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
{-

A multi-threaded PAB simulator

-}
module Plutus.PAB.Simulator(
    Simulation
    , runSimulatorEffects
    , test
    ) where

import           Control.Lens                             (makeLenses, view)
import           Control.Monad                            (forM)
import           Control.Monad.Freer                      (Eff, Member, interpret, reinterpret, runM, send, subsume,
                                                           type (~>))
import           Control.Monad.Freer.Error                (Error, runError)
import           Control.Monad.Freer.Extras.Log           (LogMessage, LogMsg (..), LogObserve, handleLogWriter,
                                                           handleObserveLog, logInfo, mapLog)
import           Control.Monad.Freer.Extras.Modify        (raiseEnd7, writeIntoState)
import           Control.Monad.Freer.State                (State, gets, runState)
import           Control.Monad.Freer.Writer               (Writer)
import           Data.Text                                (Text)
import           Wallet.Emulator.MultiAgent               (EmulatorTimeEvent (..))
import           Wallet.Emulator.Wallet                   (Wallet (..), WalletEvent (..))

import           Plutus.PAB.Core.ContractInstance         as ContractInstance
import           Plutus.PAB.Effects.Contract.ContractTest (TestContracts (..))
import           Plutus.PAB.Effects.MultiAgent            (PABMultiAgentMsg (..), _InstanceMsg)
import           Plutus.PAB.Types                         (PABError)
import           Plutus.V1.Ledger.Slot                    (Slot)
import           Wallet.Emulator.LogMessages              (RequestHandlerLogMsg, TxBalanceMsg)
import           Wallet.Emulator.MultiAgent               (EmulatorEvent' (..), _singleton)

data SimulatorState =
    SimulatorState
        { _logMessages :: [LogMessage PABMultiAgentMsg]
        , _currentSlot :: Slot
        }
    deriving Show

makeLenses ''SimulatorState

type SimulatorEffects effs =
    LogMsg TxBalanceMsg
    ': LogMsg RequestHandlerLogMsg
    ': LogMsg (ContractInstanceMsg TestContracts)
    ': LogObserve (LogMessage Text)
    ': LogMsg Text
    ': Error PABError
    ': effs

type Simulation a = Eff (SimulatorEffects '[IO]) a

handleSimulator ::
    forall a.
    Wallet
    -> Eff (SimulatorEffects '[IO]) a
    -> IO (Either PABError a, SimulatorState)
handleSimulator wallet action = do
    let action' :: Eff (SimulatorEffects '[IO, Writer [LogMessage PABMultiAgentMsg], Error PABError, State SimulatorState, IO]) a = raiseEnd7 action
    runM
        $ runState initialState
        $ runError
        $ interpret (writeIntoState logMessages)
        $ subsume @IO
        $ subsume @(Error PABError)
        $ interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter _singleton)
        $ reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
        $ reinterpret (timed @EmulatorEvent')
        $ reinterpret (mapLog (WalletEvent wallet . GenericLog))
        $ handleObserveLog
        $ interpret (handleLogWriter _InstanceMsg)
        $ interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter _singleton)
        $ reinterpret (mapLog @_ @PABMultiAgentMsg EmulatorMsg)
        $ reinterpret (timed @EmulatorEvent')
        $ reinterpret (mapLog (WalletEvent wallet . RequestHandlerLog))
        $ interpret @(LogMsg PABMultiAgentMsg) (handleLogWriter _singleton)
        $ reinterpret (mapLog EmulatorMsg)
        $ reinterpret (timed @EmulatorEvent')
        $ reinterpret (mapLog (WalletEvent wallet . TxBalanceLog))
        $ action'

initialState :: SimulatorState
initialState =
    SimulatorState
        { _logMessages = mempty
        , _currentSlot = 0
        }

runSimulatorEffects ::
    forall a.
    Simulation a
    -> IO (Either PABError a, SimulatorState)
runSimulatorEffects = handleSimulator (Wallet 1)

test :: IO ()
test = do
    result <- runSimulatorEffects $ do
        logInfo @(ContractInstanceMsg TestContracts) InboxMessageMatchesIteration
    print result

-- | Annotate log messages with the current slot number.
timed ::
    forall e effs.
    ( Member (State SimulatorState) effs
    , Member (LogMsg (EmulatorTimeEvent e)) effs
    )
    => LogMsg e
    ~> Eff effs
timed = \case
    LMessage m -> do
        m' <- forM m $ \msg -> do
            sl <- gets (view currentSlot)
            pure (EmulatorTimeEvent sl msg)
        send (LMessage m')

-- TODO
-- 1. Make timed emulator event
-- 2. Handler for node client effect
