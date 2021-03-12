{-# LANGUAGE AllowAmbiguousTypes        #-}
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
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StrictData                 #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

-- | A test version of the 'App' stack which runs all operations in memory.
-- No networking, no filesystem.
module Plutus.PAB.MockApp
    ( runScenario
    , MockAppEffects
    , defaultWallet
    , TestState
    , agentStates
    , emulatorEventLog
    , initialTestState
    -- * Queries of the emulated state
    , valueAt
    , TxCounts(..)
    , txCounts
    , txValidated
    , txMemPool
    , blockchainNewestFirst
    ) where

import qualified Cardano.Node.Types                       as NodeServer
import           Control.Lens                             hiding (use)
import           Control.Monad.Freer                      (Eff, Member)
import           Control.Monad.Freer.Error                (Error)
import           Control.Monad.Freer.Extras.Log           (LogMessage, LogMsg)
import           Control.Monad.Freer.Extras.State         (use)
import           Control.Monad.Freer.State                (State)
import           Control.Monad.Freer.Writer               (Writer)
import           Data.Map                                 (Map)
import qualified Data.Map                                 as Map
import           Data.Text                                (Text)
import           Data.Text.Prettyprint.Doc
import qualified Plutus.Contract.Trace           as Trace
import           Ledger                                   (Address, Blockchain)
import qualified Ledger
import qualified Ledger.AddressMap                        as AM
import           Plutus.PAB.Command                       ()
import           Plutus.PAB.Effects.Contract.ContractTest (ContractTestMsg)
import           Plutus.PAB.Effects.MultiAgent            (PABMultiAgentMsg)
import           Plutus.PAB.Effects.UUID                  (UUIDEffect)
import           Plutus.PAB.Simulator                     (AgentState)
import           Plutus.PAB.Types                         (PABError (..))
import           Test.QuickCheck.Instances.UUID           ()

import           Cardano.Node.Types                       (MockServerLogMsg)
import           Wallet.API                               (WalletAPIError)
import           Wallet.Emulator.Chain                    (ChainControlEffect (..), ChainEffect, ChainEvent, ChainState)
import qualified Wallet.Emulator.Chain
import           Wallet.Emulator.ChainIndex               (ChainIndexEvent)
import           Wallet.Emulator.MultiAgent               (EmulatorEvent)
import           Wallet.Emulator.Wallet                   (Wallet (..))

data TestState =
    TestState
        { _agentStates      :: Map Wallet AgentState
        , _nodeState        :: NodeServer.AppState
        , _emulatorEventLog :: [LogMessage MockAppLog]
        }


data MockAppLog =
    MockAppEmulatorLog EmulatorEvent
    | MockAppContractTest ContractTestMsg
    | MockAppMultiAgent PABMultiAgentMsg
    | MockAppMetadata Text

instance Pretty MockAppLog where
    pretty = \case
        MockAppEmulatorLog e  -> pretty e
        MockAppContractTest e -> pretty e
        MockAppMultiAgent e   -> pretty e
        MockAppMetadata e     -> pretty e

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
    '[ ChainControlEffect
    --  , MultiAgentPABEffect
     , ChainEffect
     ]

data MockAppReport =
    MockAppReport
        { marFinalChainEvents      :: [LogMessage MockServerLogMsg]
        , marFinalEmulatorEvents   :: [LogMessage MockAppLog]
        , marFinalChainIndexEvents :: [LogMessage ChainIndexEvent]
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

runScenario ::
  Eff '[ ChainControlEffect
    --    , MultiAgentPABEffect
       , ChainEffect
       , LogMsg ContractTestMsg
       , LogMsg ChainEvent
       , Writer [LogMessage PABMultiAgentMsg]
       , Writer [LogMessage MockAppLog]
       , State ChainState
       , State (Map Wallet AgentState)
       , Error WalletAPIError
       , Error PABError
       , State TestState
       , UUIDEffect
       , IO] a
  -> IO a
runScenario = undefined -- FIXME: implement runScenario
    -- (result, finalState) <- runMockApp initialTestState $ do
    --             -- void Wallet.Emulator.Chain.processBlock
    --             action
    -- case result of
    --     Left err -> do
    --         void $ runMockApp finalState $ do
    --             chainEvents <- use (nodeState . NodeServer.eventHistory)
    --             emulatorEvents <- use emulatorEventLog
    --             chainIndexEvents <- undefined -- FIXME: get chainIndexEvents

    --             let theReport = MockAppReport (toList chainEvents) emulatorEvents (toList chainIndexEvents)
    --                 doc = renderStrict . layoutPretty defaultLayoutOptions . pretty $ theReport
    --             liftIO $ putStrLn $ Text.unpack doc
    --         error $ show err
    --     Right value -> pure value
--   action
--     & handleTopLevelEffects
--     & handleLogMessages emulatorTime
--     & handleWriters
--     & handleStates
--     & handleErrors
--     & handleFinalEffects state
--   where
--     emulatorTime = view (nodeState .  NodeServer.chainState . Wallet.Emulator.Chain.currentSlot) state

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
--   Note that the agents may have a different view of this (use 'processAllMsgBoxes'
--   to process all agent's message boxes)
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
