{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

-- | A test version of the 'App' stack which runs all operations in memory.
-- No networking, no filesystem.
module Plutus.SCB.TestApp
    ( runScenario
    , sync
    , syncAll
    , TestAppEffects
    , valueAt
    , defaultWallet
    ) where

import           Cardano.Node.Follower                         (NodeFollowerEffect, handleNodeFollower)
import qualified Cardano.Node.Follower                         as NodeFollower
import           Cardano.Node.Mock                             (NodeServerEffects)
import qualified Cardano.Node.Mock                             as NodeServer
import           Cardano.Node.RandomTx                         (GenRandomTx, runGenRandomTx)
import           Cardano.Node.Types                            (AppState, FollowerID, NodeFollowerState)
import qualified Cardano.Node.Types                            as NodeServer
import qualified Cardano.Wallet.Mock                           as WalletServer
import           Control.Concurrent.MVar                       (MVar, newMVar)
import           Control.Lens                                  hiding (use)
import           Control.Monad                                 (void)
import           Control.Monad.Except                          (ExceptT, MonadError, runExceptT)
import           Control.Monad.Freer
import           Control.Monad.Freer                           (Eff, interpret, interpretM, runM)
import           Control.Monad.Freer.Error                     (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extra.Log                 (Log, logDebug, logInfo, runStderrLog)
import           Control.Monad.Freer.Extra.State               (assign, use)
import           Control.Monad.Freer.Extras
import qualified Control.Monad.Freer.Log                       as EmulatorLog
import           Control.Monad.Freer.State                     (State, runState)
import           Control.Monad.Freer.Writer                    (Writer, runWriter)
import           Control.Monad.IO.Class                        (MonadIO, liftIO)
import           Control.Monad.Logger                          (LoggingT, MonadLogger, logDebugN, logInfoN,
                                                                runStderrLoggingT)
import           Data.Aeson                                    as JSON
import           Data.Aeson.Types                              as JSON
import           Data.Bifunctor                                (first)
import           Data.Foldable                                 (toList, traverse_)
import           Data.Map                                      (Map)
import qualified Data.Map                                      as Map
import qualified Data.Sequence                                 as Seq
import           Data.Text                                     (Text)
import qualified Data.Text                                     as Text
import           Eventful                                      (commandStoredAggregate, getLatestStreamProjection,
                                                                streamEventEvent)
import           Eventful.Store.Memory                         (EventMap, emptyEventMap, stateEventStoreReader,
                                                                stateEventStoreWriter, stateGlobalEventStoreReader)
import           Language.Plutus.Contract.Resumable            (ResumableError)
import           Language.Plutus.Contract.Servant              (initialResponse, runUpdate)
import qualified Language.PlutusTx.Coordination.Contracts.Game as Contracts.Game
import           Ledger                                        (Address)
import qualified Ledger
import           Ledger.AddressMap                             (UtxoMap)
import qualified Ledger.AddressMap                             as AM
import           Plutus.SCB.Command                            ()
import           Plutus.SCB.Core
import           Plutus.SCB.Effects.Contract                   (ContractEffect (..))
import           Plutus.SCB.Effects.ContractTest               (TestContracts, handleContractTest)
import           Plutus.SCB.Effects.EventLog                   (EventLogEffect, handleEventLogSql, handleEventLogState)
import           Plutus.SCB.Effects.MultiAgent                 (AgentState, MultiAgentSCBEffect)
import qualified Plutus.SCB.Effects.MultiAgent                 as SCB.MultiAgent
import           Plutus.SCB.Effects.UUID                       (UUIDEffect, handleUUIDEffect)
import           Plutus.SCB.Events                             (ChainEvent)
import           Plutus.SCB.Query                              (pureProjection)
import           Plutus.SCB.Types                              (SCBError (..), _WalletError)
import           Plutus.SCB.Utils                              (abbreviate, tshow)
import           Test.QuickCheck.Instances.UUID                ()

import qualified Cardano.ChainIndex.Server                     as ChainIndex
import qualified Cardano.ChainIndex.Types                      as ChainIndex
import           Wallet.API                                    (WalletAPIError, addSignatures, ownOutputs, ownPubKey,
                                                                startWatching, submitTxn, updatePaymentWithChange,
                                                                watchedAddresses)
import           Wallet.Effects                                (ChainIndexEffect, NodeClientEffect,
                                                                SigningProcessEffect, WalletEffect)
import           Wallet.Emulator.Chain                         (ChainEffect, ChainState, handleChain)
import qualified Wallet.Emulator.Chain
import           Wallet.Emulator.ChainIndex                    (ChainIndexControlEffect, ChainIndexState,
                                                                handleChainIndex, handleChainIndexControl)
import qualified Wallet.Emulator.ChainIndex                    as ChainIndex
import           Wallet.Emulator.MultiAgent                    (EmulatorEvent, chainEvent, chainIndexEvent,
                                                                walletClientEvent, walletEvent)
import           Wallet.Emulator.NodeClient                    (NodeClientState, NodeControlEffect, handleNodeClient,
                                                                handleNodeControl)
import qualified Wallet.Emulator.NodeClient
import           Wallet.Emulator.SigningProcess                (SigningProcess, SigningProcessControlEffect,
                                                                handleSigningProcess, handleSigningProcessControl)
import qualified Wallet.Emulator.SigningProcess                as SP
import           Wallet.Emulator.Wallet                        (Wallet (..), WalletState)
import qualified Wallet.Emulator.Wallet

data TestState =
    TestState
        { _eventStore       :: EventMap (ChainEvent TestContracts)
        , _agentStates      :: Map Wallet AgentState
        , _nodeState        :: NodeServer.AppState
        , _chainEventLog    :: [ChainEvent TestContracts]
        , _emulatorEventLog :: [EmulatorEvent]
        }

makeLenses 'TestState

defaultWallet :: Wallet
defaultWallet = WalletServer.activeWallet

initialTestState :: TestState
initialTestState =
    TestState
        { _eventStore = emptyEventMap
        , _agentStates = Map.empty
        , _nodeState = NodeServer.initialAppState
        , _chainEventLog = []
        , _emulatorEventLog = []
        }

type TestAppEffects =
    '[ MultiAgentSCBEffect
     , ChainEffect
     , EventLogEffect (ChainEvent TestContracts)
     , State TestState
     , Log
     , IO
     ]

-- | The value at an address, in the UTXO set of the emulated node.
--   Note that the agents may have a different view of this (use 'syncAll'
--   to synchronise all agents)
valueAt :: Member (State TestState) effs => Address -> Eff effs Ledger.Value
valueAt address =
    use (nodeState
        . NodeServer.chainState
        . Wallet.Emulator.Chain.chainNewestFirst
        . to (AM.values . AM.fromChain)
        . at address
        . non mempty
        )

runScenario :: Eff TestAppEffects a -> IO ()
runScenario action = do
    let testState = initialTestState
    (result, finalState) <- runTestApp initialTestState $ do
                Wallet.Emulator.Chain.processBlock
                syncAll
                void action
    case result of
        Left err -> do
            runTestApp finalState $ do
                events :: [ChainEvent TestContracts] <-
                    fmap streamEventEvent <$> runGlobalQuery pureProjection
                logDebug "Final Event Stream"
                logDebug "--"
                traverse_ (logDebug . abbreviate 120 . tshow) events
                logDebug "--"
                logDebug "Final chain events"
                logDebug "--"
                chainEvents <- use (nodeState . NodeServer.eventHistory)
                traverse_ (logDebug . abbreviate 120 . tshow) chainEvents
                logDebug "--"
                logDebug "Final emulator events"
                logDebug "--"
                chainEvents <- use emulatorEventLog
                traverse_ (logDebug . abbreviate 120 . tshow) chainEvents
                logDebug "--"
                logDebug "Final chain index events (default wallet)"
                logDebug "--"
                chainIndexEvents <- use (agentStates . at defaultWallet . anon (SCB.MultiAgent.emptyAgentState defaultWallet) (const False) . SCB.MultiAgent.chainIndexState  . ChainIndex.indexEvents)
                traverse_ (logDebug . abbreviate 120 . tshow) chainIndexEvents
                logDebug "--"
            error $ show err
        Right _ -> pure ()

runTestApp ::
       TestState -> Eff TestAppEffects () -> IO (Either SCBError (), TestState)
runTestApp state action =
    runM
    $ handleUUIDEffect
    $ runState state

    -- error handlers
    $ runError
    $ flip handleError (throwError . WalletError)

    -- state handlers
    $ interpret (handleZoomedState eventStore)
    $ interpret (handleZoomedState agentStates)
    $ interpret (handleZoomedState (nodeState . NodeServer.chainState))
    $ interpret (handleZoomedState (nodeState . NodeServer.followerState))

    -- writers
    $ interpret (writeIntoState emulatorEventLog)
    $ interpret (writeIntoState chainEventLog)
    $ interpret (handleZoomedWriter @[EmulatorEvent] @_ @[Wallet.Emulator.Chain.ChainEvent] (below chainEvent))

    -- handlers for 'TestAppEffects'
    $ subsume
    $ runStderrLog
    $ subsume
    $ handleEventLogState
    $ handleChain
    $ SCB.MultiAgent.handleMultiAgent
    $ raiseEnd6
        -- interpret the 'TestAppEffects' using
        -- the following list of effects
        @'[ Writer [Wallet.Emulator.Chain.ChainEvent]
          , Writer [ChainEvent TestContracts]
          , Writer [EmulatorEvent]

          , State _
          , State _
          , State (Map Wallet AgentState)
          , State (EventMap (ChainEvent TestContracts))

          , Error WalletAPIError
          , Error SCBError

          , State TestState

          , UUIDEffect
          , IO
          ]
        action

-- | Synchronise the agent's view of the blockchain with the node.
sync :: Member MultiAgentSCBEffect effs => Wallet -> Eff effs ()
sync wllt = SCB.MultiAgent.agentControlAction wllt ChainIndex.syncState

-- | Run 'sync' for all agents
syncAll :: Member MultiAgentSCBEffect effs => Eff effs ()
syncAll = traverse_ sync (Wallet <$> [1..10])

fromString :: Either String a -> Either SCBError a
fromString = first (ContractCommandError 0 . Text.pack)
