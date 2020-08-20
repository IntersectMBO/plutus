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
{-# LANGUAGE StrictData                 #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

-- | A test version of the 'App' stack which runs all operations in memory.
-- No networking, no filesystem.
module Plutus.SCB.MockApp
    ( runScenario
    , sync
    , syncAll
    , MockAppEffects
    , defaultWallet
    , TestState
    -- * Queries of the emulated state
    , valueAt
    , TxCounts(..)
    , txCounts
    , txValidated
    , txMemPool
    , blockchainNewestFirst
    ) where

import qualified Cardano.Node.Types                    as NodeServer
import           Control.Lens                          hiding (use)
import           Control.Monad                         (void)
import           Control.Monad.Freer                   (Eff, Member, interpret, runM, subsume)
import           Control.Monad.Freer.Error             (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extra.Log         (LogMsg)
import           Control.Monad.Freer.Extra.State       (use)
import           Control.Monad.Freer.Extras
import           Control.Monad.Freer.Log               (LogLevel (Info), LogMessage, handleLogWriter, logMessage)
import           Control.Monad.Freer.State             (State, runState)
import           Control.Monad.Freer.Writer            (Writer)
import           Control.Monad.IO.Class                (MonadIO (..))
import           Data.Foldable                         (toList, traverse_)
import           Data.Map                              (Map)
import qualified Data.Map                              as Map
import qualified Data.Text                             as Text
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import qualified Language.Plutus.Contract.Trace        as Trace
import           Ledger                                (Address, Blockchain)
import qualified Ledger
import qualified Ledger.AddressMap                     as AM
import           Plutus.SCB.Command                    ()
import           Plutus.SCB.Core
import           Plutus.SCB.Effects.ContractTest       (ContractTestMsg, TestContracts)
import           Plutus.SCB.Effects.MultiAgent         (AgentState, MultiAgentSCBEffect, SCBMultiAgentMsg)
import qualified Plutus.SCB.Effects.MultiAgent         as SCB.MultiAgent
import           Plutus.SCB.Effects.UUID               (UUIDEffect, handleUUIDEffect)
import           Plutus.SCB.Types                      (SCBError (..))
import           Test.QuickCheck.Instances.UUID        ()

import qualified Cardano.ChainIndex.Server             as ChainIndex
import qualified Cardano.ChainIndex.Types              as ChainIndex
import           Cardano.Node.Follower                 (NodeFollowerLogMsg)
import           Wallet.API                            (WalletAPIError)
import           Wallet.Emulator.Chain                 (ChainControlEffect, ChainEffect, ChainEvent, handleChain,
                                                        handleControlChain)
import qualified Wallet.Emulator.Chain
import           Wallet.Emulator.ChainIndex            (ChainIndexEvent)
import           Wallet.Emulator.MultiAgent            (emulatorTimeEvent, _singleton)
import           Wallet.Emulator.MultiAgent            (EmulatorEvent, chainEvent)
import           Wallet.Emulator.Wallet                (Wallet (..))

data TestState =
    TestState
        { _agentStates      :: Map Wallet AgentState
        , _nodeState        :: NodeServer.AppState
        , _emulatorEventLog :: [LogMessage MockAppLog]
        }


data MockAppLog =
    MockAppEmulatorLog EmulatorEvent
    | MockAppContractTest ContractTestMsg
    | MockAppNodeFollower NodeFollowerLogMsg
    | MockAppMultiAgent SCBMultiAgentMsg

instance Pretty MockAppLog where
    pretty = \case
        MockAppEmulatorLog e -> pretty e
        MockAppContractTest e -> pretty e
        MockAppNodeFollower e -> pretty e
        MockAppMultiAgent e -> pretty e

makeLenses 'TestState
makeClassyPrisms ''MockAppLog

defaultWallet :: Wallet
defaultWallet = Wallet 1

initialTestState :: TestState
initialTestState =
    TestState
        { _agentStates = Map.empty
        , _nodeState = NodeServer.initialAppState Trace.allWallets
        , _emulatorEventLog = []
        }

type MockAppEffects =
    '[ MultiAgentSCBEffect
     , ChainControlEffect
     , ChainEffect
     , State TestState
     , Error SCBError
     , IO
     ]

data MockAppReport =
    MockAppReport
        { marFinalChainEvents      :: [ChainEvent]
        , marFinalEmulatorEvents   :: [LogMessage MockAppLog]
        , marFinalChainIndexEvents :: [ChainIndexEvent]
        }

instance Pretty MockAppReport where
    pretty MockAppReport{marFinalChainEvents, marFinalEmulatorEvents, marFinalChainIndexEvents} =
        let hr = "--" in
        vsep
        [ "Final chain events"
        , hr
        , vsep (pretty <$> marFinalChainEvents)
        , hr
        , "Final emulator events"
        , hr
        , vsep (pretty <$> marFinalEmulatorEvents)
        , hr
        , "Final chain index events (default wallet)"
        , hr
        , vsep (pretty <$> marFinalChainIndexEvents)
        ]

runScenario :: Eff MockAppEffects a -> IO a
runScenario action = do
    (result, finalState) <- runMockApp initialTestState $ do
                void Wallet.Emulator.Chain.processBlock
                syncAll
                action
    case result of
        Left err -> do
            void $ runMockApp finalState $ do
                chainEvents <- use (nodeState . NodeServer.eventHistory)
                emulatorEvents <- use emulatorEventLog
                chainIndexEvents <- use (agentStates . at defaultWallet . anon (SCB.MultiAgent.emptyAgentState defaultWallet) (const False) . SCB.MultiAgent.chainIndexState  . ChainIndex.indexEvents)

                let theReport = MockAppReport (toList chainEvents) emulatorEvents (toList chainIndexEvents)
                    doc = renderStrict . layoutPretty defaultLayoutOptions . pretty $ theReport
                liftIO $ putStrLn $ Text.unpack doc
            error $ show err
        Right value -> pure value

runMockApp ::
       TestState -> Eff MockAppEffects a -> IO (Either SCBError a, TestState)
runMockApp state action =
    let emulatorTime = view (nodeState .  NodeServer.chainState . Wallet.Emulator.Chain.currentSlot) state in
    runM
    $ handleUUIDEffect
    $ runState state

    -- error handlers
    $ runError
    $ flip handleError (throwError . WalletError)

    -- state handlers
    $ interpret (handleZoomedState agentStates)
    $ interpret (handleZoomedState (nodeState . NodeServer.chainState))
    $ interpret (handleZoomedState (nodeState . NodeServer.followerState))

    -- writers
    $ interpret (writeIntoState emulatorEventLog)
    $ interpret (handleZoomedWriter @[LogMessage MockAppLog] @_ @[Wallet.Emulator.Chain.ChainEvent] (below (logMessage Info . _MockAppEmulatorLog . emulatorTimeEvent emulatorTime . chainEvent)))
    $ interpret (handleZoomedWriter @[LogMessage MockAppLog] @_ @[LogMessage SCBMultiAgentMsg] (below (below _MockAppMultiAgent)))

    -- log messages
    $ interpret (handleLogWriter @NodeFollowerLogMsg @[LogMessage MockAppLog] (_singleton . below _MockAppNodeFollower))
    $ interpret (handleLogWriter @ContractTestMsg @[LogMessage MockAppLog] (_singleton . below _MockAppContractTest))

    -- handlers for 'MockAppEffects'
    $ subsume
    $ subsume
    $ subsume
    $ handleChain
    $ handleControlChain
    $ SCB.MultiAgent.handleMultiAgent
    $ raiseEnd6
        -- interpret the 'MockAppEffects' using
        -- the following list of effects
        @'[ LogMsg ContractTestMsg
          , LogMsg NodeFollowerLogMsg
          , Writer [LogMessage SCBMultiAgentMsg]
          , Writer [Wallet.Emulator.Chain.ChainEvent]
          , Writer [LogMessage MockAppLog]

          , State _
          , State _
          , State (Map Wallet AgentState)

          , Error WalletAPIError
          , Error SCBError

          , State TestState

          , UUIDEffect
          , IO
          ]
        action

-- | Synchronise the agent's view of the blockchain with the node.
sync ::
    forall effs.
    ( Member MultiAgentSCBEffect effs
    )
    => Wallet
    -> Eff effs ()
sync wllt = do
    SCB.MultiAgent.agentControlAction wllt ChainIndex.syncState
    SCB.MultiAgent.agentAction wllt $ do
        processAllContractInboxes @TestContracts
        processAllContractOutboxes @TestContracts Trace.defaultMaxIterations

-- | Run 'sync' for all agents
syncAll :: Member MultiAgentSCBEffect effs => Eff effs ()
syncAll = traverse_ sync (Wallet <$> [1..10])

-- | Statistics about the transactions that have been validated by the emulated node.
data TxCounts =
    TxCounts
        { _txValidated :: Int
        -- ^ How many transactions were checked and added to the ledger
        , _txMemPool   :: Int
        -- ^ How many transactions remain in the mempool of the emulated node
        } deriving (Eq, Ord, Show)

txCounts :: Member (State TestState) effs => Eff effs TxCounts
txCounts = do
    chain <- use blockchainNewestFirst
    pool <- use (nodeState . NodeServer.chainState . Wallet.Emulator.Chain.txPool)
    return
        $ TxCounts
            { _txValidated = lengthOf folded chain
            , _txMemPool   = length pool
            }

blockchainNewestFirst :: Lens' TestState Blockchain
blockchainNewestFirst = nodeState . NodeServer.chainState . Wallet.Emulator.Chain.chainNewestFirst

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

makeLenses ''TxCounts
