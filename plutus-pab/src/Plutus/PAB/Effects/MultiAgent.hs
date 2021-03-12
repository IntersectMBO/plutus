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
    -- * Multi-agent effect
    PABMultiAgentMsg(..)
    -- * Misc.
    , _InstanceMsg
    , _LogMessageText
    ) where

import           Cardano.Metadata.Types                   (MetadataLogMessage)
import           Control.Lens                             (AReview, below, makeClassyPrisms)
import           Control.Monad.Freer.Extras.Log           (LogMessage)
import qualified Data.Text                                as T
import           Data.Text.Prettyprint.Doc

import           Cardano.ChainIndex.Server                (ChainIndexServerMsg)
import           Ledger.Slot                              (Slot)

import           Plutus.PAB.Core                          (CoreMsg)
import           Plutus.PAB.Core.ContractInstance         (ContractInstanceMsg)
import           Plutus.PAB.Effects.Contract.ContractTest (ContractTestMsg, TestContracts (..))
import           Plutus.PAB.Effects.ContractRuntime       (ContractRuntimeMsg)

import           Wallet.Emulator.MultiAgent               (EmulatorEvent, _singleton, emulatorTimeEvent, walletEvent)
import           Wallet.Emulator.Wallet                   (Wallet)
import qualified Wallet.Emulator.Wallet                   as Wallet

-- $multiagent
-- An PAB version of 'Wallet.Emulator.MultiAgent', with agent-specific states and actions on them.
-- Agents are represented by the 'Wallet' type.
-- Each agent corresponds to one PAB, with its own view of the world, all acting
-- on the same blockchain.

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

_InstanceMsg :: AReview [LogMessage PABMultiAgentMsg] (LogMessage (ContractInstanceMsg TestContracts))
_InstanceMsg = _singleton . below _ContractInstanceLog

_LogMessageText :: Slot -> Wallet -> AReview [LogMessage PABMultiAgentMsg] (LogMessage T.Text)
_LogMessageText s w = _singleton . below (_EmulatorMsg . emulatorTimeEvent s . walletEvent w . Wallet._GenericLog)
