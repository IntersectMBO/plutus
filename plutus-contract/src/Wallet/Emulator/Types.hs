{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
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
    EmulatorEvent(..),
    EmulatorAction(..),
    -- ** Wallet state
    WalletState(..),
    emptyWalletState,
    ownPrivateKey,
    ownAddress,
    -- ** Traces
    runTraceChain,
    runTraceTxPool,
    evalTraceTxPool,
    execTraceTxPool,
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
    MonadEmulator,
    processEmulated,
    runWalletActionAndProcessPending,
    runWalletControlActionAndProcessPending,
    fundsDistribution,
    emLog,
    selectCoin
    ) where

import           Control.Lens               hiding (index)
import           Control.Monad.Except
import qualified Control.Monad.Freer        as Eff
import qualified Control.Monad.Freer.Error  as Eff
import qualified Control.Monad.Freer.Extras as Eff
import           Control.Monad.State
import           Data.Foldable              (traverse_)
import qualified Data.Text                  as T
import           Prelude                    as P

import           Ledger
import           Wallet.API                 (WalletAPIError (..))

import           Wallet.Emulator.Chain      as Chain
import           Wallet.Emulator.ChainIndex
import           Wallet.Emulator.MultiAgent
import           Wallet.Emulator.NodeClient
import           Wallet.Emulator.Wallet

type EmulatorEffs = '[MultiAgentEffect, ChainEffect]

-- | Notify the given 'Wallet' of some blockchain events.
walletRecvBlocks :: Eff.Members EmulatorEffs effs => Wallet -> [ChainClientNotification] -> Eff.Eff effs ()
walletRecvBlocks w nots = void $ walletControlAction w (traverse_ go nots) where
    go noti = clientNotify noti >> chainIndexNotify noti

-- | Notify the given 'Wallet' that a block has been validated.
walletNotifyBlock :: Eff.Members EmulatorEffs effs => Wallet -> Block -> Eff.Eff effs ()
walletNotifyBlock w block = do
    sl <- Chain.getCurrentSlot
    walletRecvBlocks w [BlockValidated block, SlotChanged sl]

-- | Notify a list of 'Wallet's that a block has been validated.
walletsNotifyBlock :: forall effs . Eff.Members EmulatorEffs effs => [Wallet] -> Block -> Eff.Eff effs ()
walletsNotifyBlock wls b = mapM_ (\w -> walletNotifyBlock w b) wls

-- | Validate all pending transactions.
processPending :: forall effs . Eff.Members EmulatorEffs effs => Eff.Eff effs Block
processPending = processBlock

-- | Add a number of empty blocks to the blockchain, by performing
--   'processPending' @n@ times.
addBlocks :: Eff.Members EmulatorEffs effs => Integer -> Eff.Eff effs [Block]
addBlocks i = traverse (const processPending) [1..i]

-- | Add a number of blocks, notifying all the given 'Wallet's after each block.
addBlocksAndNotify :: Eff.Members EmulatorEffs effs => [Wallet] -> Integer -> Eff.Eff effs [Block]
addBlocksAndNotify wallets i =
    let run = do
            block <- processPending
            walletsNotifyBlock wallets block
            pure block
    in traverse (const run) [1..i]

type MonadEmulator e m = (MonadError e m, AsAssertionError e, MonadState EmulatorState m)

newtype EmulatorAction e a = EmulatorAction { unEmulatorAction :: ExceptT e (State EmulatorState) a }
    deriving newtype (Functor, Applicative, Monad, MonadState EmulatorState, MonadError e)

processEmulated :: forall m e a . (MonadEmulator e m) => Eff.Eff EmulatorEffs a -> m a
processEmulated act =
    act
        & Eff.raiseEnd2
        & handleMultiAgent
        & handleChain
        & Eff.interpret (Eff.handleZoomedWriter p1)
        & Eff.interpret (Eff.handleZoomedState chainState)
        & Eff.interpret (Eff.writeIntoState emulatorLog)
        -- HACK
        & flip Eff.handleError (\(e :: WalletAPIError) -> Eff.throwError $ GenericAssertion $ T.pack $ show e)
        & Eff.interpret (Eff.handleZoomedError p2)
        & Eff.interpretM Eff.stateToMonadState
        & Eff.interpretM Eff.errorToMonadError
        & Eff.runM
    where
        p1 :: Prism' [EmulatorEvent] [ChainEvent]
        p1 = below chainEvent
        p2 :: Prism' e AssertionError
        p2 = _AssertionError

-- | Run a 'MonadEmulator' action on an 'EmulatorState', returning the final
--   state and either the result or an 'AssertionError'.
runEmulator :: forall e a . EmulatorState -> EmulatorAction e a -> (Either e a, EmulatorState)
runEmulator e a = runState (runExceptT $ unEmulatorAction a) e

-- | Run an 'Trace' on a blockchain.
runTraceChain :: Blockchain -> Eff.Eff EmulatorEffs a -> (Either AssertionError a, EmulatorState)
runTraceChain ch t = runState (runExceptT $ processEmulated t) emState where
    emState = emulatorState ch

-- | Run a 'Trace' on an empty blockchain with a pool of pending transactions.
runTraceTxPool :: TxPool -> Eff.Eff EmulatorEffs a -> (Either AssertionError a, EmulatorState)
runTraceTxPool tp t = runState (runExceptT $ processEmulated t) emState where
    emState = emulatorStatePool tp

-- | Evaluate a 'Trace' on an empty blockchain with a pool of pending
--   transactions and return the final value, discarding the final
--   'EmulatorState'.
evalTraceTxPool :: TxPool -> Eff.Eff EmulatorEffs a -> Either AssertionError a
evalTraceTxPool pl t = fst $ runTraceTxPool pl t

-- | Evaluate a 'Trace' on an empty blockchain with a pool of pending
--   transactions and return the final 'EmulatorState', discarding the final
--   value.
execTraceTxPool :: TxPool -> Eff.Eff EmulatorEffs a -> EmulatorState
execTraceTxPool pl t = snd $ runTraceTxPool pl t

-- | Run an action as a wallet, subsequently process any pending transactions
--   and notify wallets. Returns the new block
runWalletActionAndProcessPending
    :: Eff.Members EmulatorEffs effs
    => [Wallet]
    -> Wallet
    -> Eff.Eff EmulatedWalletEffects a
    -> Eff.Eff effs ([Tx], a)
runWalletActionAndProcessPending wallets wallet action = do
    result <- walletAction wallet action
    block <- addBlocksAndNotify wallets 1
    pure (concat block, result)

-- | Run a control action as a wallet, subsequently process any pending
--   transactions and notify wallets. Returns the new block.
runWalletControlActionAndProcessPending
    :: Eff.Members EmulatorEffs effs
    => [Wallet]
    -> Wallet
    -> Eff.Eff EmulatedWalletControlEffects a
    -> Eff.Eff effs ([Tx], a)
runWalletControlActionAndProcessPending wallets wallet action = do
    result <- walletControlAction wallet action
    block <- addBlocksAndNotify wallets 1
    pure (concat block, result)
