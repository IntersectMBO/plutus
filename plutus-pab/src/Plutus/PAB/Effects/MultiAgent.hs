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

-- FIXME: Replace with PABLogMsg / Move to types?
