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
    -- * Multi-agent effect -- FIXME move to Simulator?
    PABMultiAgentMsg(..)
    ) where

import           Cardano.Metadata.Types                   (MetadataLogMessage)
import qualified Data.Text                                as T
import           Data.Text.Prettyprint.Doc

import           Cardano.ChainIndex.Server                (ChainIndexServerMsg)

import           Plutus.PAB.Core                          (CoreMsg)
import           Plutus.PAB.Core.ContractInstance         (ContractInstanceMsg)
import           Plutus.PAB.Effects.Contract.ContractTest (ContractTestMsg, TestContracts (..))
import           Plutus.PAB.Effects.ContractRuntime       (ContractRuntimeMsg)

import           Wallet.Emulator.MultiAgent               (EmulatorEvent)

-- FIXME: Replace with PABLogMsg?
data PABMultiAgentMsg =
    EmulatorMsg EmulatorEvent
    | ContractMsg ContractTestMsg
    | MetadataLog MetadataLogMessage
    | ChainIndexServerLog ChainIndexServerMsg
    | ContractInstanceLog (ContractInstanceMsg TestContracts)
    | CoreLog (CoreMsg TestContracts)
    | RuntimeLog ContractRuntimeMsg
    | UserLog T.Text
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
        UserLog m             -> pretty m
