{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
module Plutus.PAB.Effects.MultiAgent(
    -- $multiagent
    -- * Agent state
    AgentState
    , walletState
    , nodeClientState
    , chainIndexState
    , signingProcessState
    , emptyAgentState
    -- * Multi-agent effect
    , MultiAgentPABEffect(..)
    , PABMultiAgentMsg(..)
    , PABClientEffects
    , PABControlEffects
    , agentAction
    , agentControlAction
    , handleMultiAgent
    -- * Misc.
    , _InstanceMsg
    , _LogMessageText
    ) where

import           Cardano.Metadata.Server                  (handleMetadata)
import           Cardano.Metadata.Types                   (MetadataEffect, MetadataLogMessage)
import           Control.Lens                             (AReview, Lens', Prism', anon, at, below, makeClassyPrisms,
                                                           makeLenses, (&))
import           Control.Monad.Freer                      (Eff, Members, interpret, subsume, type (~>))
import           Control.Monad.Freer.Error                (Error, handleError, throwError)
import           Control.Monad.Freer.Extras.Log           (LogLevel (..), LogMessage, LogMsg, LogObserve,
                                                           handleLogWriter, handleObserveLog, logMessage)
import           Control.Monad.Freer.Extras.Modify        (handleZoomedState, handleZoomedWriter, raiseEnd)
import           Control.Monad.Freer.State                (State)
import           Control.Monad.Freer.TH                   (makeEffect)
import           Control.Monad.Freer.Writer               (Writer)
import           Data.Map                                 (Map)
import qualified Data.Text                                as T
import           Data.Text.Prettyprint.Doc
import           Eventful.Store.Memory                    (EventMap, emptyEventMap)

import           Cardano.ChainIndex.Server                (ChainIndexServerMsg)
import qualified Cardano.ChainIndex.Types                 as CI
import           Ledger.Slot                              (Slot)

import           Plutus.PAB.Core                          (CoreMsg)
import           Plutus.PAB.Core.ContractInstance         (ContractInstanceMsg)
import           Plutus.PAB.Effects.Contract              (ContractEffect (..))
import           Plutus.PAB.Effects.Contract.ContractTest (ContractTestMsg, TestContracts (..), handleContractTest)
import           Plutus.PAB.Effects.ContractRuntime       (ContractRuntimeMsg, handleContractRuntime)
import           Plutus.PAB.Effects.EventLog              (EventLogEffect, handleEventLogState)
import           Plutus.PAB.Effects.UUID                  (UUIDEffect)
import           Plutus.PAB.Events                        (PABEvent)
import           Plutus.PAB.Types                         (PABError (..))

import           Wallet.Effects                           (ChainIndexEffect, ContractRuntimeEffect, NodeClientEffect,
                                                           WalletEffect)
import qualified Wallet.Emulator.Chain                    as Chain
import           Wallet.Emulator.ChainIndex               (ChainIndexControlEffect)
import qualified Wallet.Emulator.ChainIndex               as ChainIndex
import           Wallet.Emulator.Error                    (WalletAPIError)
import           Wallet.Emulator.MultiAgent               (EmulatorEvent, EmulatorTimeEvent, _singleton,
                                                           chainIndexEvent, emulatorTimeEvent, walletClientEvent,
                                                           walletEvent)
import           Wallet.Emulator.NodeClient               (NodeClientControlEffect, NodeClientEvent)
import qualified Wallet.Emulator.NodeClient               as NC
import           Wallet.Emulator.Wallet                   (SigningProcess, SigningProcessControlEffect, Wallet,
                                                           WalletState, defaultSigningProcess,
                                                           handleSigningProcessControl)
import qualified Wallet.Emulator.Wallet                   as Wallet

-- $multiagent
-- An PAB version of 'Wallet.Emulator.MultiAgent', with agent-specific states and actions on them.
-- Agents are represented by the 'Wallet' type.
-- Each agent corresponds to one PAB, with its own view of the world, all acting
-- on the same blockchain.

data AgentState =
        AgentState
        { _walletState         :: WalletState
        , _nodeClientState     :: NC.NodeClientState
        , _chainIndexState     :: CI.AppState
        , _signingProcessState :: SigningProcess
        , _agentEventState     :: EventMap (PABEvent TestContracts)
        }

makeLenses 'AgentState

emptyAgentState :: Wallet -> AgentState
emptyAgentState wallet =
    AgentState
        { _walletState = Wallet.emptyWalletState wallet
        , _nodeClientState = NC.emptyNodeClientState
        , _chainIndexState = CI.initialAppState
        , _signingProcessState = defaultSigningProcess wallet
        , _agentEventState = emptyEventMap
        }

agentState :: Wallet.Wallet -> Lens' (Map Wallet AgentState) AgentState
agentState wallet = at wallet . anon (emptyAgentState wallet) (const False)

data PABMultiAgentMsg =
    EmulatorMsg EmulatorEvent
    | ContractMsg ContractTestMsg
    | MetadataLog MetadataLogMessage
    | ChainIndexServerLog ChainIndexServerMsg
    | ContractInstanceLog (ContractInstanceMsg TestContracts)
    | CoreLog (CoreMsg TestContracts)
    | RuntimeLog ContractRuntimeMsg
    deriving Show

instance Pretty PABMultiAgentMsg where
    pretty = \case
        EmulatorMsg m         -> pretty m
        ContractMsg m         -> pretty m
        MetadataLog m         -> pretty m
        ChainIndexServerLog m -> pretty m
        ContractInstanceLog m -> pretty m
        CoreLog m             -> pretty m
        RuntimeLog m          -> pretty m

makeClassyPrisms ''PABMultiAgentMsg

type PABClientEffects =
    '[WalletEffect
    , ContractRuntimeEffect
    , ContractEffect TestContracts
    , MetadataEffect
    , NodeClientEffect
    , ChainIndexEffect
    , UUIDEffect
    , EventLogEffect (PABEvent TestContracts)
    , Error WalletAPIError
    , Error PABError
    , LogMsg NodeClientEvent
    , LogMsg (ContractInstanceMsg TestContracts)
    , LogMsg (CoreMsg TestContracts)
    , LogMsg MetadataLogMessage
    , LogObserve (LogMessage T.Text)
    , LogMsg T.Text
    ]

type PABControlEffects =
    '[ChainIndexControlEffect
    , MetadataEffect
    , NodeClientControlEffect
    , SigningProcessControlEffect
    , State CI.AppState
    , LogMsg NodeClientEvent
    , LogMsg ChainIndexServerMsg
    , LogMsg MetadataLogMessage
    , LogMsg T.Text
    ]

type MultiAgentEffs =
    '[State (Map Wallet AgentState)
    , State Chain.ChainState
    , Error WalletAPIError
    , Chain.ChainEffect
    , Error PABError
    , LogMsg ContractTestMsg
    , Writer [LogMessage PABMultiAgentMsg]
    , UUIDEffect
    ]

data MultiAgentPABEffect r where
  AgentAction :: Wallet.Wallet -> Eff PABClientEffects r -> MultiAgentPABEffect r
  AgentControlAction :: Wallet.Wallet -> Eff PABControlEffects r -> MultiAgentPABEffect r

makeEffect ''MultiAgentPABEffect

handleMultiAgent
    :: forall effs. Members MultiAgentEffs effs
    => Eff (MultiAgentPABEffect ': effs) ~> Eff effs
handleMultiAgent = undefined
--  interpret $ \effect -> do
--   emulatorTime <- Chain.getCurrentSlot
--   let
--       timed :: forall e. Prism' (EmulatorTimeEvent e) e
--       timed = emulatorTimeEvent emulatorTime
--   case effect of
--     AgentAction wallet action -> do
--         let
--             p1 :: AReview [LogMessage PABMultiAgentMsg] [Wallet.WalletEvent]
--             p1 = below (logMessage Info . _EmulatorMsg . timed . walletEvent wallet)
--             p2 :: AReview [LogMessage PABMultiAgentMsg] (LogMessage NC.NodeClientEvent)
--             p2 = _singleton . below (_EmulatorMsg . timed . walletClientEvent wallet)
--             p3 :: AReview [LogMessage PABMultiAgentMsg] (LogMessage ChainIndex.ChainIndexEvent)
--             p3 = _singleton . below (_EmulatorMsg . timed . chainIndexEvent wallet)
--             p6 :: AReview [LogMessage PABMultiAgentMsg] (LogMessage (CoreMsg TestContracts))
--             p6 = _singleton . below _CoreLog
--             p7 :: AReview [LogMessage PABMultiAgentMsg] (LogMessage MetadataLogMessage)
--             p7 = _singleton . below _MetadataLog
--             p8 :: AReview [LogMessage PABMultiAgentMsg] (LogMessage ContractRuntimeMsg)
--             p8 = _singleton . below _RuntimeLog
--         action
--             & raiseEnd16
--             & Wallet.handleWallet
--             & interpret (handleContractRuntime @TestContracts @IO)
--             & handleContractTest
--             & handleMetadata
--             & NC.handleNodeClient
--             & ChainIndex.handleChainIndex
--             & subsume
--             & handleEventLogState
--             & subsume
--             & subsume
--             & interpret (handleLogWriter p2)
--             & interpret (handleLogWriter _InstanceMsg)
--             & interpret (handleLogWriter p6)
--             & interpret (handleLogWriter p7)
--             & handleObserveLog
--             & interpret (handleLogWriter (_LogMessageText emulatorTime wallet))
--             & interpret (handleZoomedState (agentState wallet . walletState))
--             & interpret (handleZoomedWriter p1)
--             & interpret (handleLogWriter p8)
--             & interpret (handleZoomedState (agentState wallet . nodeClientState))
--             & interpret (handleZoomedWriter p2)
--             & interpret (handleZoomedState (agentState wallet . chainIndexState . CI.indexState))
--             & interpret (handleLogWriter p3)
--             & interpret (handleZoomedState (agentState wallet . signingProcessState))
--             & interpret (handleZoomedState (agentState wallet . agentEventState))
--             & flip handleError (throwError  . MetadataError)
--     AgentControlAction wallet action -> do
--         let
--             p1 :: AReview [LogMessage PABMultiAgentMsg] [Wallet.WalletEvent]
--             p1 = below (logMessage Info . _EmulatorMsg . timed . walletEvent wallet)
--             p2 :: AReview [LogMessage PABMultiAgentMsg] (LogMessage NC.NodeClientEvent)
--             p2 = _singleton . below (_EmulatorMsg . timed . walletClientEvent wallet)
--             p3 :: AReview [LogMessage PABMultiAgentMsg] (LogMessage ChainIndex.ChainIndexEvent)
--             p3 = _singleton . below (_EmulatorMsg . timed . chainIndexEvent wallet)
--             p4 :: AReview [LogMessage PABMultiAgentMsg] (LogMessage T.Text)
--             p4 = _singleton . below (_EmulatorMsg . timed . walletEvent wallet . Wallet._GenericLog)
--             p5 :: AReview [LogMessage PABMultiAgentMsg] (LogMessage ChainIndexServerMsg)
--             p5 = _singleton . below _ChainIndexServerLog
--             p6 :: AReview [LogMessage PABMultiAgentMsg] (LogMessage MetadataLogMessage)
--             p6 = _singleton . below _MetadataLog
--         action
--             & raiseEnd9
--             & ChainIndex.handleChainIndexControl
--             & handleMetadata
--             -- & NF.handleNodeFollower
--             & NC.handleNodeControl
--             & handleSigningProcessControl
--             & interpret (handleZoomedState (agentState wallet . chainIndexState))
--             & interpret (handleLogWriter p2)
--             & interpret (handleLogWriter p5)
--             & interpret (handleLogWriter p6)
--             & interpret (handleLogWriter p4)
--             & interpret (handleZoomedState (agentState wallet . walletState))
--             & interpret (handleZoomedWriter p1)
--             & interpret (handleZoomedState (agentState wallet . nodeClientState))
--             & interpret (handleZoomedWriter p2)
--             & interpret (handleZoomedState (agentState wallet . chainIndexState . CI.indexState))
--             & interpret (handleLogWriter p3)
--             & interpret (handleZoomedState (agentState wallet . signingProcessState))
--             & flip handleError (throwError  . MetadataError)

_InstanceMsg :: AReview [LogMessage PABMultiAgentMsg] (LogMessage (ContractInstanceMsg TestContracts))
_InstanceMsg = _singleton . below _ContractInstanceLog

_LogMessageText :: Slot -> Wallet -> AReview [LogMessage PABMultiAgentMsg] (LogMessage T.Text)
_LogMessageText s w = _singleton . below (_EmulatorMsg . emulatorTimeEvent s . walletEvent w . Wallet._GenericLog)
