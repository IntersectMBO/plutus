{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Wallet.Emulator.Types(
    -- * Wallets
    Wallet(..),
    WalletId(..),
    Crypto.XPrv,
    Crypto.XPub,
    walletPubKey,
    addSignature,
    knownWallets,
    knownWallet,
    WalletNumber(..),
    toWalletNumber,
    fromWalletNumber,
    TxPool,
    -- * Emulator
    EmulatorEffs,
    Assertion(OwnFundsEqual, IsValidated),
    assert,
    assertIsValidated,
    AssertionError(..),
    AsAssertionError(..),
    ChainClientNotification(..),
    EmulatorEvent,
    EmulatorEvent',
    EmulatorTimeEvent(..),
    -- ** Wallet state
    WalletState(..),
    emptyWalletState,
    ownPrivateKey,
    ownAddress,
    -- ** Traces
    walletAction,
    assertion,
    assertOwnFundsEq,
    ownFundsEqual,
    -- * Emulator internals
    EmulatorState(..),
    emptyEmulatorState,
    emulatorState,
    emulatorStatePool,
    emulatorStateInitialDist,
    txPool,
    walletStates,
    index,
    chainState,
    currentSlot,
    processEmulated,
    fundsDistribution,
    emLog,
    selectCoin
    ) where

import qualified Cardano.Crypto.Wallet          as Crypto
import           Control.Lens                   hiding (index)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error      (Error)
import qualified Control.Monad.Freer.Extras     as Eff
import           Control.Monad.Freer.Extras.Log (LogMsg, mapLog)
import           Control.Monad.Freer.State      (State)

import           Ledger
import           Plutus.ChainIndex              (ChainIndexError)
import           Wallet.API                     (WalletAPIError (..))

import           Ledger.Fee                     (FeeConfig)
import           Ledger.TimeSlot                (SlotConfig)
import           Wallet.Emulator.Chain
import           Wallet.Emulator.MultiAgent
import           Wallet.Emulator.NodeClient
import           Wallet.Emulator.Wallet
import           Wallet.Types                   (AsAssertionError (..), AssertionError (..))

type EmulatorEffs = '[MultiAgentEffect, ChainEffect, ChainControlEffect]

processEmulated :: forall effs.
    ( Member (Error WalletAPIError) effs
    , Member (Error ChainIndexError) effs
    , Member (Error AssertionError) effs
    , Member (State EmulatorState) effs
    , Member (LogMsg EmulatorEvent') effs
    )
    => SlotConfig
    -> FeeConfig
    -> Eff (MultiAgentEffect ': MultiAgentControlEffect ': ChainEffect ': ChainControlEffect ': effs)
    ~> Eff effs
processEmulated slotCfg feeCfg act =
    act
        & handleMultiAgent feeCfg
        & handleMultiAgentControl
        & reinterpret2 @ChainEffect @(State ChainState) @(LogMsg ChainEvent) (handleChain slotCfg)
        & interpret (Eff.handleZoomedState chainState)
        & interpret (mapLog (review chainEvent))
        & reinterpret2 @ChainControlEffect @(State ChainState) @(LogMsg ChainEvent) handleControlChain
        & interpret (Eff.handleZoomedState chainState)
        & interpret (mapLog (review chainEvent))
