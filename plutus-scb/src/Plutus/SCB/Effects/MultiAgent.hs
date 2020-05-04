{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}
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
    , SCBClientEffects
    , SCBControlEffects
    , agentAction
    , agentControlAction
    , handleMultiAgent
    ) where

import           Control.Lens                    (Lens', Prism', anon, at, below, makeLenses, (&))
import           Control.Monad.Freer             (Eff, Members, type (~>), interpret, subsume)
import           Control.Monad.Freer.Error       (Error)
import           Control.Monad.Freer.Extra.Log   (Log)
import           Control.Monad.Freer.Extras      (handleZoomedState, handleZoomedWriter, raiseEnd11, raiseEnd6)
import qualified Control.Monad.Freer.Log         as Log
import           Control.Monad.Freer.State       (State)
import           Control.Monad.Freer.TH          (makeEffect)
import           Control.Monad.Freer.Writer      (Writer)
import           Data.Map                        (Map)
import           Eventful.Store.Memory           (EventMap, emptyEventMap)

import qualified Cardano.ChainIndex.Types        as CI
import           Cardano.Node.Follower           (NodeFollowerEffect)
import qualified Cardano.Node.Follower           as NF
import qualified Cardano.Node.Types              as NF

import           Plutus.SCB.Effects.Contract     (ContractEffect (..))
import           Plutus.SCB.Effects.ContractTest (TestContracts (..), handleContractTest)
import           Plutus.SCB.Effects.EventLog     (EventLogEffect, handleEventLogState)
import           Plutus.SCB.Effects.UUID         (UUIDEffect)
import           Plutus.SCB.Events               (ChainEvent)
import           Plutus.SCB.Types                (SCBError (..))

import           Wallet.Effects                  (ChainIndexEffect, NodeClientEffect, SigningProcessEffect,
                                                  WalletEffect)
import qualified Wallet.Emulator.Chain           as Chain
import           Wallet.Emulator.ChainIndex      (ChainIndexControlEffect)
import qualified Wallet.Emulator.ChainIndex      as ChainIndex
import           Wallet.Emulator.Error           (WalletAPIError)
import           Wallet.Emulator.MultiAgent      (EmulatorEvent, chainIndexEvent, walletClientEvent, walletEvent)
import           Wallet.Emulator.NodeClient      (NodeClientControlEffect)
import qualified Wallet.Emulator.NodeClient      as NC
import           Wallet.Emulator.SigningProcess  (SigningProcessControlEffect)
import qualified Wallet.Emulator.SigningProcess  as SP
import           Wallet.Emulator.Wallet          (Wallet, WalletState)
import qualified Wallet.Emulator.Wallet          as Wallet

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

type SCBClientEffects =
    '[WalletEffect
    , ContractEffect TestContracts
    , NodeClientEffect
    , ChainIndexEffect
    , SigningProcessEffect
    , UUIDEffect
    , EventLogEffect (ChainEvent TestContracts)
    , NodeFollowerEffect
    , Error WalletAPIError
    , Error SCBError
    , Log
    ]

type SCBControlEffects =
    '[ChainIndexControlEffect
    , NodeFollowerEffect
    , NodeClientControlEffect
    , SigningProcessControlEffect
    , State CI.AppState
    , Log
    ]

type MultiAgentEffs =
    '[State (Map Wallet AgentState)
    , State Chain.ChainState
    , State NF.NodeFollowerState
    , Error WalletAPIError
    , Chain.ChainEffect
    , Error SCBError
    , Writer [EmulatorEvent]
    , UUIDEffect
    ]

data MultiAgentSCBEffect r where
  AgentAction :: Wallet.Wallet -> Eff SCBClientEffects r -> MultiAgentSCBEffect r
  AgentControlAction :: Wallet.Wallet -> Eff SCBControlEffects r -> MultiAgentSCBEffect r

makeEffect ''MultiAgentSCBEffect

handleMultiAgent
    :: forall effs. Members MultiAgentEffs effs
    => Eff (MultiAgentSCBEffect ': effs) ~> Eff effs
handleMultiAgent = interpret $ \case
    AgentAction wallet action ->
        action
            & raiseEnd11
            & Wallet.handleWallet
            & handleContractTest
            & NC.handleNodeClient
            & ChainIndex.handleChainIndex
            & SP.handleSigningProcess
            & subsume
            & handleEventLogState
            & NF.handleNodeFollower
            & subsume
            & subsume
            & interpret (handleZoomedWriter p4)
            & interpret (handleZoomedState (agentState wallet . walletState))
            & interpret (handleZoomedWriter p1)
            & interpret (handleZoomedState (agentState wallet . nodeClientState))
            & interpret (handleZoomedWriter p2)
            & interpret (handleZoomedState (agentState wallet . chainIndexState . CI.indexState))
            & interpret (handleZoomedWriter p3)
            & interpret (handleZoomedState (agentState wallet . signingProcessState))
            & interpret (handleZoomedState (agentState wallet . agentEventState))
            where
                p1 :: Prism' [EmulatorEvent] [Wallet.WalletEvent]
                p1 = below (walletEvent wallet)
                p2 :: Prism' [EmulatorEvent] [NC.NodeClientEvent]
                p2 = below (walletClientEvent wallet)
                p3 :: Prism' [EmulatorEvent] [ChainIndex.ChainIndexEvent]
                p3 = below (chainIndexEvent wallet)
                p4 :: Prism' [EmulatorEvent] [Log.LogMessage]
                p4 = below (walletEvent wallet . Wallet._WalletMsg)
    AgentControlAction wallet action ->
        action
            & raiseEnd6
            & ChainIndex.handleChainIndexControl
            & NF.handleNodeFollower
            & NC.handleNodeControl
            & SP.handleSigningProcessControl
            & interpret (handleZoomedState (agentState wallet . chainIndexState))
            & interpret (handleZoomedWriter p4)
            & interpret (handleZoomedState (agentState wallet . walletState))
            & interpret (handleZoomedWriter p1)
            & interpret (handleZoomedState (agentState wallet . nodeClientState))
            & interpret (handleZoomedWriter p2)
            & interpret (handleZoomedState (agentState wallet . chainIndexState . CI.indexState))
            & interpret (handleZoomedWriter p3)
            & interpret (handleZoomedState (agentState wallet . signingProcessState))
            where
                p1 :: Prism' [EmulatorEvent] [Wallet.WalletEvent]
                p1 = below (walletEvent wallet)
                p2 :: Prism' [EmulatorEvent] [NC.NodeClientEvent]
                p2 = below (walletClientEvent wallet)
                p3 :: Prism' [EmulatorEvent] [ChainIndex.ChainIndexEvent]
                p3 = below (chainIndexEvent wallet)
                p4 :: Prism' [EmulatorEvent] [Log.LogMessage]
                p4 = below (walletEvent wallet . Wallet._WalletMsg)
