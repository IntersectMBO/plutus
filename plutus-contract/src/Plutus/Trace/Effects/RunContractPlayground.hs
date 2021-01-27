{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

-- | A version of 'Plutus.Trace.Effects.RunContract' for use in the
--   playground.
module Plutus.Trace.Effects.RunContractPlayground(
    RunContractPlayground
    , callEndpoint
    , launchContract
    , handleRunContractPlayground
    ) where

import           Control.Lens
import           Control.Monad                           (void)
import           Control.Monad.Freer                     (Eff, Member, interpret, reinterpret, type (~>))
import           Control.Monad.Freer.Coroutine           (Yield)
import           Control.Monad.Freer.Error               (Error, throwError)
import           Control.Monad.Freer.Log                 (LogMsg (..), mapLog)
import           Control.Monad.Freer.Reader              (ask, runReader)
import           Control.Monad.Freer.State               (State, gets, modify)
import           Control.Monad.Freer.TH                  (makeEffect)
import qualified Data.Aeson                              as JSON
import           Data.Map                                (Map)
import           Language.Plutus.Contract                (Contract (..), ContractInstanceId, EndpointDescription (..),
                                                          HasBlockchainActions)
import           Plutus.Trace.Effects.ContractInstanceId (ContractInstanceIdEff, nextId)
import           Plutus.Trace.Emulator.ContractInstance  (EmulatorRuntimeError, contractThread, getThread)
import           Plutus.Trace.Emulator.Types             (ContractConstraints, ContractHandle (..),
                                                          EmulatorMessage (..), EmulatorRuntimeError (..),
                                                          EmulatorThreads, walletInstanceTag)
import           Plutus.Trace.Scheduler                  (Priority (..), SysCall (..), SystemCall, ThreadId, fork,
                                                          mkSysCall)
import           Wallet.Emulator.MultiAgent              (EmulatorEvent' (..), MultiAgentEffect)
import           Wallet.Emulator.Wallet                  (Wallet)
import           Wallet.Types                            (EndpointValue (..))

{- Note [Wallet contract instances]

In the Playground we have a single 'Contract' that we are testing, and each
wallet runs exactly one instance of this contract. As a result,

1. The 'RunContractPlayground' effect, which governs interactions with contract
   instances, only needs a 'Wallet' to identify the contract instance.
2. We don't need an @ActivateContract@ action, we can just start all the
   instances at the beginning of the simulation, using 'launchContract'

-}

data RunContractPlayground r where
    LaunchContract :: Wallet -> RunContractPlayground ()
    CallEndpoint :: Wallet -> String -> JSON.Value -> RunContractPlayground ()

makeEffect ''RunContractPlayground

-- | Handle the 'RunContractPlayground' effect.
handleRunContractPlayground ::
    forall s e effs effs2.
    ( HasBlockchainActions s
    , ContractConstraints s
    , Show e
    , JSON.ToJSON e
    , Member ContractInstanceIdEff effs
    , Member (Yield (SystemCall effs2 EmulatorMessage) (Maybe EmulatorMessage)) effs
    , Member (LogMsg EmulatorEvent') effs2
    , Member (Error EmulatorRuntimeError) effs2
    , Member (State EmulatorThreads) effs2
    , Member MultiAgentEffect effs2
    , Member (State (Map Wallet ContractInstanceId)) effs2
    , Member (State (Map Wallet ContractInstanceId)) effs
    )
    => Contract s e ()
    -> RunContractPlayground
    ~> Eff effs
handleRunContractPlayground contract = \case
    CallEndpoint wallet ep vl -> handleCallEndpoint @effs @effs2 wallet ep vl
    LaunchContract wllt       -> handleLaunchContract @s @e @effs @effs2 contract wllt

handleLaunchContract ::
    forall s e effs effs2.
    ( HasBlockchainActions s
    , ContractConstraints s
    , Show e
    , JSON.ToJSON e
    , Member (Yield (SystemCall effs2 EmulatorMessage) (Maybe EmulatorMessage)) effs
    , Member ContractInstanceIdEff effs
    , Member (LogMsg EmulatorEvent') effs2
    , Member (Error EmulatorRuntimeError) effs2
    , Member (State EmulatorThreads) effs2
    , Member MultiAgentEffect effs2
    , Member (State (Map Wallet ContractInstanceId)) effs
    )
    => Contract s e ()
    -> Wallet
    -> Eff effs ()
handleLaunchContract contract wllt = do
    i <- nextId
    let handle = ContractHandle{chContract=contract, chInstanceId = i, chInstanceTag = walletInstanceTag wllt}
    void $ fork @effs2 @EmulatorMessage "contract instance" Normal (runReader wllt $ interpret (mapLog InstanceEvent) $ reinterpret (mapLog InstanceEvent) $ contractThread handle)
    modify @(Map Wallet ContractInstanceId) (set (at wllt) (Just i))

handleCallEndpoint ::
    forall effs effs2.
    ( Member (State (Map Wallet ContractInstanceId)) effs2
    , Member (Error EmulatorRuntimeError) effs2
    , Member (Yield (SystemCall effs2 EmulatorMessage) (Maybe EmulatorMessage)) effs
    , Member (State EmulatorThreads) effs2
    )
    => Wallet
    -> String
    -> JSON.Value
    -> Eff effs ()
handleCallEndpoint wllt endpointName endpointValue = do
    let epJson = JSON.object ["tag" JSON..= endpointName, "value" JSON..= EndpointValue endpointValue]
        thr = do
            threadId <- getInstance wllt >>= getThread
            ownId <- ask @ThreadId
            void $ mkSysCall @effs2 @EmulatorMessage Normal (Message threadId $ EndpointCall ownId (EndpointDescription endpointName) epJson)
    void $ fork @effs2 @EmulatorMessage "call endpoint" Normal thr

getInstance ::
    ( Member (State (Map Wallet ContractInstanceId)) effs
    , Member (Error EmulatorRuntimeError) effs
    )
    => Wallet
    -> Eff effs ContractInstanceId
getInstance wllt = do
    r <- gets @(Map Wallet ContractInstanceId) (view (at wllt))
    case r of
        Nothing -> throwError (InstanceIdNotFound wllt)
        Just i  -> pure i
