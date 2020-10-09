{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Wallet.Emulator.Types(
    -- * Wallets
    Wallet(..),
    walletPubKey,
    walletPrivKey,
    signWithWallet,
    addSignature,
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
    EmulatorBackend,
    -- ** Wallet state
    WalletState(..),
    emptyWalletState,
    ownPrivateKey,
    ownAddress,
    -- ** Traces
    walletAction,
    walletRecvBlocks,
    walletNotifyBlock,
    walletsNotifyBlock,
    processPending,
    addBlocks,
    addBlocksAndNotify,
    assertion,
    assertOwnFundsEq,
    ownFundsEqual,
    runEmulator,
    -- * Emulator internals
    EmulatorState(..),
    emptyEmulatorState,
    emulatorState,
    emulatorStatePool,
    emulatorStateInitialDist,
    chainNewestFirst,
    chainOldestFirst,
    txPool,
    walletStates,
    walletClientStates,
    index,
    chainState,
    currentSlot,
    processEmulated,
    runWalletActionAndProcessPending,
    runWalletControlActionAndProcessPending,
    fundsDistribution,
    emLog,
    selectCoin
    ) where

import           Control.Lens               hiding (index)
import           Control.Monad.Except
import           Control.Monad.Freer
import           Control.Monad.Freer.Error  (Error)
import qualified Control.Monad.Freer.Error  as Eff
import qualified Control.Monad.Freer.Extras as Eff
import           Control.Monad.Freer.Log    (LogLevel (..), LogMessage, logMessage)
import           Control.Monad.Freer.State  (State)
import qualified Control.Monad.Freer.State  as Eff
import           Data.Foldable              (traverse_)
import qualified Data.Text                  as T
import           Prelude                    as P

import           Ledger
import           Wallet.API                 (WalletAPIError (..))

import           Wallet.Emulator.Chain      as Chain
import           Wallet.Emulator.ChainIndex
import           Wallet.Emulator.MultiAgent
import           Wallet.Emulator.NodeClient
import           Wallet.Emulator.Notify     (EmulatorContractNotifyEffect (..))
import           Wallet.Emulator.Wallet
import           Wallet.Types               (AsAssertionError (..), AssertionError (..))

type EmulatorEffs = '[MultiAgentEffect, ChainEffect, ChainControlEffect]

-- | Notify the given 'Wallet' of some blockchain events.
walletRecvBlocks :: Members EmulatorEffs effs => Wallet -> [ChainClientNotification] -> Eff effs ()
walletRecvBlocks w nots = void $ walletControlAction w (traverse_ go nots) where
    go noti = clientNotify noti >> chainIndexNotify noti

-- | Notify the given 'Wallet' that a block has been validated.
walletNotifyBlock :: Members EmulatorEffs effs => Wallet -> Block -> Eff effs ()
walletNotifyBlock w block = do
    sl <- Chain.getCurrentSlot
    walletRecvBlocks w [BlockValidated block, SlotChanged sl]

-- | Notify a list of 'Wallet's that a block has been validated.
walletsNotifyBlock :: forall effs . Members EmulatorEffs effs => [Wallet] -> Block -> Eff effs ()
walletsNotifyBlock wls b = mapM_ (\w -> walletNotifyBlock w b) wls

-- | Validate all pending transactions.
processPending :: forall effs . Members EmulatorEffs effs => Eff effs Block
processPending = processBlock

-- | Add a number of empty blocks to the blockchain, by performing
--   'processPending' @n@ times.
addBlocks :: Members EmulatorEffs effs => Integer -> Eff effs [Block]
addBlocks i = traverse (const processPending) [1..i]

-- | Add a number of blocks, notifying all the given 'Wallet's after each block.
addBlocksAndNotify :: Members EmulatorEffs effs => [Wallet] -> Integer -> Eff effs [Block]
addBlocksAndNotify wallets i =
    let go = do
            block <- processPending
            walletsNotifyBlock wallets block
            pure block
    in traverse (const go) [1..i]

type EmulatorBackend e =
    '[ Error e
    , State EmulatorState
    ]

processEmulated :: forall e effs.
    ( AsAssertionError e
    , Member (Error e) effs
    , Member (State EmulatorState) effs
    , Member EmulatorContractNotifyEffect effs
    )
    => Eff EmulatorEffs
    ~> Eff effs
processEmulated act = do
    emulatorTime <- Eff.gets (view $ chainState . currentSlot)
    let
        p1 :: Prism' [LogMessage EmulatorEvent] [ChainEvent]
        p1 =  below (logMessage Info . emulatorTimeEvent emulatorTime . chainEvent)
        p2 :: Prism' e AssertionError
        p2 = _AssertionError
    act
        & Eff.raiseEnd3
        & handleMultiAgent
        & handleChain
        & handleControlChain
        & interpret (Eff.handleZoomedWriter p1)
        & interpret (Eff.handleZoomedState chainState)
        & interpret (Eff.writeIntoState emulatorLog)
        -- HACK
        & flip Eff.handleError (\(e :: WalletAPIError) -> Eff.throwError $ GenericAssertion $ T.pack $ show e)
        & interpret (Eff.handleZoomedError p2)

-- | Run a 'Eff (EmulatorBackend e)' action on an 'EmulatorState', returning
--   the final state and either the result or an error.
runEmulator :: forall e a . EmulatorState -> Eff (EmulatorBackend e) a -> (Either e a, EmulatorState)
runEmulator state = run . Eff.runState state . Eff.runError

-- | Run an action as a wallet, subsequently process any pending transactions
--   and notify wallets. Returns the new block
runWalletActionAndProcessPending
    :: Members EmulatorEffs effs
    => [Wallet]
    -> Wallet
    -> Eff EmulatedWalletEffects a
    -> Eff effs ([Tx], a)
runWalletActionAndProcessPending wallets wallet action = do
    result <- walletAction wallet action
    block <- addBlocksAndNotify wallets 1
    pure (concat block, result)

-- | Run a control action as a wallet, subsequently process any pending
--   transactions and notify wallets. Returns the new block.
runWalletControlActionAndProcessPending
    :: Members EmulatorEffs effs
    => [Wallet]
    -> Wallet
    -> Eff EmulatedWalletControlEffects a
    -> Eff effs ([Tx], a)
runWalletControlActionAndProcessPending wallets wallet action = do
    result <- walletControlAction wallet action
    block <- addBlocksAndNotify wallets 1
    pure (concat block, result)
