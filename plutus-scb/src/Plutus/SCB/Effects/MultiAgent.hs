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
module Plutus.SCB.Effects.MultiAgent(
    -- $multiagent
    -- * Agent state
    AgentState
    , walletState
    , nodeClientState
    , chainIndexState
    , signingProcessState
    , emptyAgentState
    -- * Multi-agent effect
    , MultiAgentSCBEffect(..)
    , SCBMultiAgentMsg(..)
    , SCBClientEffects
    , SCBControlEffects
    , agentAction
    , agentControlAction
    , handleMultiAgent
    -- * Misc.
    , _InstanceMsg
    , _LogMessageText
    ) where

import           Cardano.Metadata.Server            (handleMetadata)
import           Cardano.Metadata.Types             (MetadataEffect, MetadataLogMessage)
import           Control.Lens                       (AReview, Lens', Prism', anon, at, below, makeClassyPrisms,
                                                     makeLenses, (&))
import           Control.Monad.Freer                (Eff, Members, interpret, subsume, type (~>))
import           Control.Monad.Freer.Error          (Error, handleError, throwError)
import           Control.Monad.Freer.Extra.Log      (LogMsg)
import           Control.Monad.Freer.Extras         (handleZoomedState, handleZoomedWriter, raiseEnd17, raiseEnd9)
import           Control.Monad.Freer.Log            (LogLevel (..), LogMessage, LogObserve, handleLogWriter,
                                                     handleObserveLog, logMessage)
import qualified Control.Monad.Freer.Log            as Log
import           Control.Monad.Freer.State          (State)
import           Control.Monad.Freer.TH             (makeEffect)
import           Control.Monad.Freer.Writer         (Writer)
import           Data.Map                           (Map)
import qualified Data.Text                          as T
import           Data.Text.Prettyprint.Doc
import           Eventful.Store.Memory              (EventMap, emptyEventMap)

import           Cardano.ChainIndex.Server          (ChainIndexServerMsg)
import qualified Cardano.ChainIndex.Types           as CI
import           Cardano.Node.Follower              (NodeFollowerEffect, NodeFollowerLogMsg)
import qualified Cardano.Node.Follower              as NF
import qualified Cardano.Node.Types                 as NF
import           Ledger.Slot                        (Slot)

import           Plutus.SCB.Core                    (CoreMsg)
import           Plutus.SCB.Core.ContractInstance   (ContractInstanceMsg)
import           Plutus.SCB.Effects.Contract        (ContractEffect (..))
import           Plutus.SCB.Effects.ContractRuntime (ContractRuntimeMsg, handleContractRuntime)
import           Plutus.SCB.Effects.ContractTest    (ContractTestMsg, TestContracts (..), handleContractTest)
import           Plutus.SCB.Effects.EventLog        (EventLogEffect, handleEventLogState)
import           Plutus.SCB.Effects.UUID            (UUIDEffect)
import           Plutus.SCB.Events                  (ChainEvent)
import           Plutus.SCB.Types                   (SCBError (..))

import           Wallet.Effects                     (ChainIndexEffect, ContractRuntimeEffect, NodeClientEffect,
                                                     SigningProcessEffect, WalletEffect)
import qualified Wallet.Emulator.Chain              as Chain
import           Wallet.Emulator.ChainIndex         (ChainIndexControlEffect)
import qualified Wallet.Emulator.ChainIndex         as ChainIndex
import           Wallet.Emulator.Error              (WalletAPIError)
import           Wallet.Emulator.MultiAgent         (EmulatorEvent, EmulatorTimeEvent, _singleton, chainIndexEvent,
                                                     emulatorTimeEvent, walletClientEvent, walletEvent)
import           Wallet.Emulator.NodeClient         (NodeClientControlEffect)
import qualified Wallet.Emulator.NodeClient         as NC
import           Wallet.Emulator.SigningProcess     (SigningProcessControlEffect)
import qualified Wallet.Emulator.SigningProcess     as SP
import           Wallet.Emulator.Wallet             (Wallet, WalletState)
import qualified Wallet.Emulator.Wallet             as Wallet

-- $multiagent
-- An SCB version of 'Wallet.Emulator.MultiAgent', with agent-specific states and actions on them.
-- Agents are represented by the 'Wallet' type.
-- Each agent corresponds to one SCB, with its own view of the world, all acting
-- on the same blockchain.

data AgentState =
        AgentState
        { _walletState         :: WalletState
        , _nodeClientState     :: NC.NodeClientState
        , _chainIndexState     :: CI.AppState
        , _signingProcessState :: SP.SigningProcess
        , _agentEventState     :: EventMap (ChainEvent TestContracts)
        }

makeLenses 'AgentState

emptyAgentState :: Wallet -> AgentState
emptyAgentState wallet =
    AgentState
        { _walletState = Wallet.emptyWalletState wallet
        , _nodeClientState = NC.emptyNodeClientState
        , _chainIndexState = CI.initialAppState
        , _signingProcessState = SP.defaultSigningProcess wallet
        , _agentEventState = emptyEventMap
        }

agentState :: Wallet.Wallet -> Lens' (Map Wallet AgentState) AgentState
agentState wallet = at wallet . anon (emptyAgentState wallet) (const False)

data SCBMultiAgentMsg =
    EmulatorMsg EmulatorEvent
    | ContractMsg ContractTestMsg
    | NodeFollowerMsg NodeFollowerLogMsg
    | MetadataLog MetadataLogMessage
    | ChainIndexServerLog ChainIndexServerMsg
    | ContractInstanceLog (ContractInstanceMsg TestContracts)
    | CoreLog (CoreMsg TestContracts)
    | RuntimeLog ContractRuntimeMsg

instance Pretty SCBMultiAgentMsg where
    pretty = \case
        EmulatorMsg m         -> pretty m
        ContractMsg m         -> pretty m
        NodeFollowerMsg m     -> pretty m
        MetadataLog m         -> pretty m
        ChainIndexServerLog m -> pretty m
        ContractInstanceLog m -> pretty m
        CoreLog m             -> pretty m
        RuntimeLog m          -> pretty m

makeClassyPrisms ''SCBMultiAgentMsg

type SCBClientEffects =
    '[WalletEffect
    , ContractRuntimeEffect
    , ContractEffect TestContracts
    , MetadataEffect
    , NodeClientEffect
    , ChainIndexEffect
    , SigningProcessEffect
    , UUIDEffect
    , EventLogEffect (ChainEvent TestContracts)
    , NodeFollowerEffect
    , Error WalletAPIError
    , Error SCBError
    , LogMsg (ContractInstanceMsg TestContracts)
    , LogMsg (CoreMsg TestContracts)
    , LogMsg MetadataLogMessage
    , LogObserve (LogMessage T.Text)
    , LogMsg T.Text
    ]

type SCBControlEffects =
    '[ChainIndexControlEffect
    , MetadataEffect
    , NodeFollowerEffect
    , NodeClientControlEffect
    , SigningProcessControlEffect
    , State CI.AppState
    , LogMsg ChainIndexServerMsg
    , LogMsg MetadataLogMessage
    , LogMsg T.Text
    ]

type MultiAgentEffs =
    '[State (Map Wallet AgentState)
    , State Chain.ChainState
    , State NF.NodeFollowerState
    , Error WalletAPIError
    , Chain.ChainEffect
    , Error SCBError
    , LogMsg ContractTestMsg
    , LogMsg NodeFollowerLogMsg
    , Writer [LogMessage SCBMultiAgentMsg]
    , UUIDEffect
    ]

data MultiAgentSCBEffect r where
  AgentAction :: Wallet.Wallet -> Eff SCBClientEffects r -> MultiAgentSCBEffect r
  AgentControlAction :: Wallet.Wallet -> Eff SCBControlEffects r -> MultiAgentSCBEffect r

makeEffect ''MultiAgentSCBEffect

handleMultiAgent
    :: forall effs. Members MultiAgentEffs effs
    => Eff (MultiAgentSCBEffect ': effs) ~> Eff effs
handleMultiAgent = interpret $ \effect -> do
  emulatorTime <- Chain.getCurrentSlot
  let
      timed :: forall e. Prism' (EmulatorTimeEvent e) e
      timed = emulatorTimeEvent emulatorTime
  case effect of
    AgentAction wallet action -> do
        let
            p1 :: AReview [LogMessage SCBMultiAgentMsg] [Wallet.WalletEvent]
            p1 = below (logMessage Info . _EmulatorMsg . timed . walletEvent wallet)
            p2 :: AReview [LogMessage SCBMultiAgentMsg] [NC.NodeClientEvent]
            p2 = below (logMessage Info . _EmulatorMsg . timed . walletClientEvent wallet)
            p3 :: AReview [LogMessage SCBMultiAgentMsg] (LogMessage ChainIndex.ChainIndexEvent)
            p3 = _singleton . below (_EmulatorMsg . timed . chainIndexEvent wallet)
            p6 :: AReview [LogMessage SCBMultiAgentMsg] (LogMessage (CoreMsg TestContracts))
            p6 = _singleton . below _CoreLog
            p7 :: AReview [LogMessage SCBMultiAgentMsg] (LogMessage MetadataLogMessage)
            p7 = _singleton . below _MetadataLog
            p8 :: AReview [LogMessage SCBMultiAgentMsg] (LogMessage ContractRuntimeMsg)
            p8 = _singleton . below _RuntimeLog
        action
            & raiseEnd17
            & Wallet.handleWallet
            & interpret (handleContractRuntime @TestContracts)
            & handleContractTest
            & handleMetadata
            & NC.handleNodeClient
            & ChainIndex.handleChainIndex
            & SP.handleSigningProcess
            & subsume
            & handleEventLogState
            & NF.handleNodeFollower
            & subsume
            & subsume
            & interpret (handleLogWriter _InstanceMsg)
            & interpret (handleLogWriter p6)
            & interpret (handleLogWriter p7)
            & handleObserveLog
            & interpret (handleLogWriter (_LogMessageText emulatorTime wallet))
            & interpret (handleZoomedState (agentState wallet . walletState))
            & interpret (handleZoomedWriter p1)
            & interpret (handleLogWriter p8)
            & interpret (handleZoomedState (agentState wallet . nodeClientState))
            & interpret (handleZoomedWriter p2)
            & interpret (handleZoomedState (agentState wallet . chainIndexState . CI.indexState))
            & interpret (handleLogWriter p3)
            & interpret (handleZoomedState (agentState wallet . signingProcessState))
            & interpret (handleZoomedState (agentState wallet . agentEventState))
            & flip handleError (throwError  . MetadataError)
    AgentControlAction wallet action -> do
        let
            p1 :: AReview [LogMessage SCBMultiAgentMsg] [Wallet.WalletEvent]
            p1 = below (logMessage Info . _EmulatorMsg . timed . walletEvent wallet)
            p2 :: AReview [LogMessage SCBMultiAgentMsg] [NC.NodeClientEvent]
            p2 = below (logMessage Info . _EmulatorMsg . timed . walletClientEvent wallet)
            p3 :: AReview [LogMessage SCBMultiAgentMsg] (LogMessage ChainIndex.ChainIndexEvent)
            p3 = _singleton . below (_EmulatorMsg . timed . chainIndexEvent wallet)
            p4 :: AReview [LogMessage SCBMultiAgentMsg] (Log.LogMessage T.Text)
            p4 = _singleton . below (_EmulatorMsg . timed . walletEvent wallet . Wallet._GenericLog)
            p5 :: AReview [LogMessage SCBMultiAgentMsg] (Log.LogMessage ChainIndexServerMsg)
            p5 = _singleton . below _ChainIndexServerLog
            p6 :: AReview [LogMessage SCBMultiAgentMsg] (Log.LogMessage MetadataLogMessage)
            p6 = _singleton . below _MetadataLog
        action
            & raiseEnd9
            & ChainIndex.handleChainIndexControl
            & handleMetadata
            & NF.handleNodeFollower
            & NC.handleNodeControl
            & SP.handleSigningProcessControl
            & interpret (handleZoomedState (agentState wallet . chainIndexState))
            & interpret (handleLogWriter p5)
            & interpret (handleLogWriter p6)
            & interpret (handleLogWriter p4)
            & interpret (handleZoomedState (agentState wallet . walletState))
            & interpret (handleZoomedWriter p1)
            & interpret (handleZoomedState (agentState wallet . nodeClientState))
            & interpret (handleZoomedWriter p2)
            & interpret (handleZoomedState (agentState wallet . chainIndexState . CI.indexState))
            & interpret (handleLogWriter p3)
            & interpret (handleZoomedState (agentState wallet . signingProcessState))
            & flip handleError (throwError  . MetadataError)

_InstanceMsg :: AReview [LogMessage SCBMultiAgentMsg] (LogMessage (ContractInstanceMsg TestContracts))
_InstanceMsg = _singleton . below _ContractInstanceLog

_LogMessageText :: Slot -> Wallet -> AReview [LogMessage SCBMultiAgentMsg] (LogMessage T.Text)
_LogMessageText s w = _singleton . below (_EmulatorMsg . emulatorTimeEvent s . walletEvent w . Wallet._GenericLog)
