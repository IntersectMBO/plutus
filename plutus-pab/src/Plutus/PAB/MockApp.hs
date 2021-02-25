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
    -- * Queries of the emulated state
    , valueAt
    , TxCounts(..)
    , txCounts
    , txValidated
    , txMemPool
    , blockchainNewestFirst
    , processMsgBox
    , processAllMsgBoxes
    ) where

import qualified Cardano.Node.Types                    as NodeServer
import           Control.Lens                          hiding (use)
import           Control.Monad                         (void)
import           Control.Monad.Freer                   (Eff, Member, interpret, reinterpret, runM, type (~>))
import           Control.Monad.Freer.Error             (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extras.Log        (LogMessage, LogMsg, handleLogWriter)
import           Control.Monad.Freer.Extras.State      (use)
import           Control.Monad.Freer.State             (State, runState)
import           Control.Monad.Freer.Writer            (Writer)
import           Control.Monad.IO.Class                (MonadIO (..))
import           Data.Foldable                         (toList, traverse_)
import           Data.Map                              (Map)
import qualified Data.Map                              as Map
import           Data.OpenUnion                        ((:++:))
import           Data.Text                             (Text)
import qualified Data.Text                             as Text
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import qualified Language.Plutus.Contract.Trace        as Trace
import           Ledger                                (Address, Blockchain, Slot)
import qualified Ledger
import qualified Ledger.AddressMap                     as AM
import           Plutus.PAB.Command                    ()
import           Plutus.PAB.Core
import           Plutus.PAB.Core.ContractInstance      (defaultMaxIterations)
import           Plutus.PAB.Effects.ContractTest       (ContractTestMsg, TestContracts)
import           Plutus.PAB.Effects.MultiAgent         (AgentState, MultiAgentPABEffect, PABMultiAgentMsg)
import qualified Plutus.PAB.Effects.MultiAgent         as PAB.MultiAgent
import           Plutus.PAB.Effects.UUID               (UUIDEffect, handleUUIDEffect)
import           Plutus.PAB.Types                      (PABError (..))
import           Test.QuickCheck.Instances.UUID        ()

import qualified Cardano.ChainIndex.Types              as ChainIndex
import           Cardano.Node.Types                    (MockServerLogMsg)
import           Control.Monad.Freer.Extras.Modify     (handleZoomedState, handleZoomedWriter, writeIntoState)
import           Wallet.API                            (WalletAPIError)
import           Wallet.Emulator.Chain                 (ChainControlEffect (..), ChainEffect, ChainEvent, ChainState,
                                                        handleChain, handleControlChain, processBlock)
import qualified Wallet.Emulator.Chain
import           Wallet.Emulator.ChainIndex            (ChainIndexEvent, chainIndexNotify)
import           Wallet.Emulator.MultiAgent            (EmulatorEvent, _singleton, chainEvent, emulatorTimeEvent)
import           Wallet.Emulator.NodeClient            (ChainClientNotification (..))
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
     , MultiAgentPABEffect
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
       , MultiAgentPABEffect
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
runScenario action = do
    (result, finalState) <- runMockApp initialTestState $ do
                void Wallet.Emulator.Chain.processBlock
                processAllMsgBoxes
                action
    case result of
        Left err -> do
            void $ runMockApp finalState $ do
                chainEvents <- use (nodeState . NodeServer.eventHistory)
                emulatorEvents <- use emulatorEventLog
                chainIndexEvents <- use (agentStates . at defaultWallet . anon (PAB.MultiAgent.emptyAgentState defaultWallet) (const False) . PAB.MultiAgent.chainIndexState  . ChainIndex.indexEvents)

                let theReport = MockAppReport (toList chainEvents) emulatorEvents (toList chainIndexEvents)
                    doc = renderStrict . layoutPretty defaultLayoutOptions . pretty $ theReport
                liftIO $ putStrLn $ Text.unpack doc
            error $ show err
        Right value -> pure value

runMockApp :: TestState
    -> Eff (MockAppEffects
            :++: '[LogMsg ContractTestMsg, LogMsg ChainEvent]
            :++: '[Writer [LogMessage PABMultiAgentMsg], Writer [LogMessage MockAppLog]]
            :++: '[State ChainState, State (Map Wallet AgentState)]
            :++: '[Error WalletAPIError]
            :++: '[Error PABError, State TestState, UUIDEffect, IO]
           ) a
    -> IO (Either PABError a, TestState)
runMockApp state action =
  action
    & handleTopLevelEffects
    & handleLogMessages emulatorTime
    & handleWriters
    & handleStates
    & handleErrors
    & handleFinalEffects state
  where
    emulatorTime = view (nodeState .  NodeServer.chainState . Wallet.Emulator.Chain.currentSlot) state

handleFinalEffects :: TestState
    -> Eff '[Error PABError, State TestState, UUIDEffect, IO] a
    -> IO (Either PABError a, TestState)
handleFinalEffects state action =
  action
    & runError
    & runState state
    & handleUUIDEffect
    & runM

notifyChainIndex ::
       ( Member ChainEffect effs
       , Member MultiAgentPABEffect effs
       )
    =>   ChainControlEffect ~> Eff (ChainControlEffect ': effs)
notifyChainIndex = \case
    ProcessBlock -> do
        block <- processBlock
        slot  <- Wallet.Emulator.Chain.getCurrentSlot
        traverse_ (notifyWallet block slot) (Wallet <$> [1..10])
        pure block
    where
        notifyWallet ::
               ( Member MultiAgentPABEffect effs)
            => Ledger.Block
            -> Slot
            -> Wallet
            -> Eff effs ()
        notifyWallet block slot wallet =
            PAB.MultiAgent.agentControlAction wallet $
                traverse_ chainIndexNotify [BlockValidated block, SlotChanged slot]

handleTopLevelEffects ::
       ( Member (State (Map Wallet AgentState)) effs
       , Member (State ChainState) effs
       , Member (Error WalletAPIError) effs
       , Member (Error PABError) effs
       , Member (LogMsg ChainEvent) effs
       , Member (Writer [LogMessage PABMultiAgentMsg]) effs
       , Member UUIDEffect effs
       , Member (LogMsg ContractTestMsg) effs
       )
    => Eff (ChainControlEffect ': MultiAgentPABEffect ': ChainEffect ': effs) ~> Eff effs
handleTopLevelEffects action =
  action
    & reinterpret notifyChainIndex
    & interpret handleControlChain
    & PAB.MultiAgent.handleMultiAgent
    & interpret handleChain

handleLogMessages ::
       Member (Writer [LogMessage MockAppLog]) effs
    => Slot
    -> Eff (LogMsg ContractTestMsg ': LogMsg ChainEvent ': effs)
    ~> Eff effs
handleLogMessages emulatorTime action =
  action
    & interpret (handleLogWriter @ContractTestMsg @[LogMessage MockAppLog] (_singleton . below _MockAppContractTest))
    & interpret (handleLogWriter @ChainEvent @[LogMessage MockAppLog] (_singleton . below (_MockAppEmulatorLog . emulatorTimeEvent emulatorTime . chainEvent)))

handleWriters ::
       Member (State TestState) effs
    => Eff (Writer [LogMessage PABMultiAgentMsg] ': Writer [LogMessage MockAppLog] ': effs)
    ~> Eff effs
handleWriters action =
  action
    & interpret (handleZoomedWriter @[LogMessage MockAppLog] @_ @[LogMessage PABMultiAgentMsg] (below (below _MockAppMultiAgent)))
    & interpret (writeIntoState emulatorEventLog)

handleStates ::
       Member (State TestState) effs
    => Eff (State ChainState ': State (Map Wallet AgentState) ': effs)
    ~> Eff effs
handleStates action =
  action
    & interpret (handleZoomedState (nodeState . NodeServer.chainState))
    & interpret (handleZoomedState agentStates)

handleErrors ::
       Member (Error PABError) effs
    => Eff (Error WalletAPIError ': effs)
    ~> Eff effs
handleErrors action =
  action
    & flip handleError (throwError . WalletError)

-- | Process wallet / contract inbox and outbox messages
processMsgBox ::
    forall effs.
    ( Member MultiAgentPABEffect effs
    )
    => Wallet
    -> Eff effs ()
processMsgBox wllt = do
    PAB.MultiAgent.agentAction wllt $ do
        processAllContractInboxes @TestContracts
        processAllContractOutboxes @TestContracts defaultMaxIterations

-- | Process the message boxes of wallets 1-10.
processAllMsgBoxes :: Member MultiAgentPABEffect effs => Eff effs ()
processAllMsgBoxes = traverse_ processMsgBox (Wallet <$> [1..10])

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
