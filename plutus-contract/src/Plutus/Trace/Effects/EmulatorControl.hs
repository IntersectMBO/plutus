{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-

An effect for inspecting & changing the internal state of the emulator.

-}
module Plutus.Trace.Effects.EmulatorControl(
    EmulatorControl(..)
    , setSigningProcess
    , agentState
    , freezeContractInstance
    , thawContractInstance
    , chainState
    , handleEmulatorControl
    ) where

import           Control.Lens                           (at, view)
import           Control.Monad                          (void)
import           Control.Monad.Freer                    (Eff, Member, type (~>))
import           Control.Monad.Freer.Coroutine          (Yield)
import           Control.Monad.Freer.Error              (Error)
import           Control.Monad.Freer.State              (State, gets)
import           Control.Monad.Freer.TH                 (makeEffect)
import           Data.Maybe                             (fromMaybe)
import           Plutus.Trace.Emulator.ContractInstance (EmulatorRuntimeError, getThread)
import           Plutus.Trace.Emulator.Types            (EmulatorMessage (Freeze), EmulatorThreads)
import           Plutus.Trace.Scheduler                 (Priority (Normal), SysCall (Message, Thaw), SystemCall,
                                                         mkSysCall)
import qualified Wallet.Emulator                        as EM
import           Wallet.Emulator.Chain                  (ChainState)
import           Wallet.Emulator.MultiAgent             (EmulatorState, MultiAgentEffect, walletControlAction)
import           Wallet.Emulator.Wallet                 (SigningProcess, Wallet, WalletState)
import qualified Wallet.Emulator.Wallet                 as W
import           Wallet.Types                           (ContractInstanceId)

{- Note [The EmulatorControl effect]

The 'EmulatorControl' effect bundles all trace actions that deal with the
internals of the Plutus emulator, such as messing with the clock and dis-
connecting agents from the network.

All other effects defined under @Plutus.Trace.Effects@ can, in theory, be run
against a live system, ie. one running in real time with a real Goguen node and
wallet(s).

This means that if you write traces in a way that doesn't require the
'Member EmulatorControl' constraint, then it is likely that your traces will
work on a live system just as they do on the emulator. (We haven't implemented
the effect handlers for "live mode" yet, so it is still possible that there
are some modifications to be made)

-}

data EmulatorControl r where
    SetSigningProcess :: Wallet -> SigningProcess -> EmulatorControl ()
    AgentState :: Wallet -> EmulatorControl WalletState
    FreezeContractInstance :: ContractInstanceId -> EmulatorControl ()
    ThawContractInstance :: ContractInstanceId -> EmulatorControl ()
    ChainState :: EmulatorControl ChainState

-- | Interpret the 'EmulatorControl' effect in the 'MultiAgentEffect' and
--   scheduler system calls.
handleEmulatorControl ::
    forall effs effs2.
    ( Member (State EmulatorThreads) effs
    , Member (State EmulatorState) effs
    , Member (Error EmulatorRuntimeError) effs
    , Member MultiAgentEffect effs
    , Member (Yield (SystemCall effs2 EmulatorMessage) (Maybe EmulatorMessage)) effs
    )
    => EmulatorControl
    ~> Eff effs
handleEmulatorControl = \case
    SetSigningProcess wllt sp -> walletControlAction wllt $ W.setSigningProcess sp
    AgentState wllt -> gets @EmulatorState (fromMaybe (W.emptyWalletState wllt) . view (EM.walletStates . at wllt))
    FreezeContractInstance i -> do
        threadId <- getThread i
        -- see note [Freeze and Thaw]
        void $ mkSysCall @effs2 @EmulatorMessage Normal (Message threadId Freeze)
    ThawContractInstance i -> do
        threadId <- getThread i
        -- see note [Freeze and Thaw]
        void $ mkSysCall @effs2 @EmulatorMessage Normal (Thaw threadId)
    ChainState -> gets (view EM.chainState)

makeEffect ''EmulatorControl
