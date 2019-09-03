{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
-- | A trace is a sequence of actions by simulated wallets that can be run
--   on the mockchain. This module contains the functions needed to build
--   traces.
module Language.Plutus.Contract.Trace(
    ContractTraceState
    , ContractTrace
    , EmulatorAction
    , ctsEvents
    , ctsContract
    , ContractTraceResult(..)
    , ctrEmulatorState
    , ctrTraceState
    , runTrace
    , execTrace
    -- * Constructing 'MonadEmulator' actions
    , runWallet
    , getHooks
    , callEndpoint
    , handleBlockchainEvents
    , addBlocks
    , addEvent
    , addEventAll
    , notifyInterestingAddresses
    , notifySlot
    -- * Running 'MonadEmulator' actions
    , MonadEmulator
    , InitialDistribution
    , withInitialDistribution
    , defaultDist
    -- * Wallets
    , EM.Wallet(..)
    , EM.walletPubKey
    , allWallets
    ) where

import           Control.Lens
import           Control.Monad                                   (void)
import           Control.Monad.Reader
import           Control.Monad.State                             (MonadState, StateT, gets, runStateT)
import           Control.Monad.Trans.Class                       (MonadTrans (..))
import           Data.Bifunctor                                  (Bifunctor (..))
import           Data.Foldable                                   (toList, traverse_)
import           Data.Map                                        (Map)
import qualified Data.Map                                        as Map
import           Data.Row
import           Data.Sequence                                   (Seq)
import qualified Data.Sequence                                   as Seq
import qualified Data.Set                                        as Set

import           Language.Plutus.Contract                        (Contract, HasWatchAddress, HasWriteTx)
import           Language.Plutus.Contract.Resumable              (ResumableError)
import qualified Language.Plutus.Contract.Resumable              as State
import           Language.Plutus.Contract.Schema                 (Event, Handlers, Input, Output)
import           Language.Plutus.Contract.Tx                     (UnbalancedTx)
import qualified Language.Plutus.Contract.Wallet                 as Wallet

import qualified Language.Plutus.Contract.Effects.AwaitSlot      as AwaitSlot
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoint
import qualified Language.Plutus.Contract.Effects.WatchAddress   as WatchAddress
import qualified Language.Plutus.Contract.Effects.WriteTx        as WriteTx

import           Ledger.Ada                                      (Ada)
import qualified Ledger.Ada                                      as Ada
import qualified Ledger.AddressMap                               as AM
import           Ledger.Slot                                     (Slot)
import           Ledger.Tx                                       (Address, Tx)

import           Wallet.Emulator                                 (AssertionError, EmulatorAction, EmulatorState,
                                                                  MonadEmulator, Wallet)
import qualified Wallet.Emulator                                 as EM

type InitialDistribution = [(Wallet, Ada)]

type ContractTrace s m a = StateT (ContractTraceState s a) m

data ContractTraceState s a =
    ContractTraceState
        { _ctsEvents   :: Map Wallet (Seq (Event s))
        -- ^ The state of the contract instance (per wallet). To get
        --   the 'Record' of a sequence of events, use
        --   'Language.Plutus.Contract.Resumable.runResumable'.
        , _ctsContract :: Contract s a
        -- ^ Current state of the contract
        }

makeLenses ''ContractTraceState

initState
    :: [Wallet]
    -> Contract s a
    -> ContractTraceState s a
initState wllts = ContractTraceState wallets where
    wallets = Map.fromList $ fmap (,mempty) wllts

-- | Add an event to the wallet's trace
addEvent :: forall s a m. MonadState (ContractTraceState s a) m => Wallet -> Event s -> m ()
addEvent w e = ctsEvents %= Map.alter go w where
    go = Just . maybe (Seq.singleton e) (|> e)

-- | Get the hooks that a contract is currently waiting for
getHooks
    :: forall s m a.
       ( Monad m
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , AllUniqueLabels (Output s)
       )
    => Wallet -> ContractTrace s m a (Either ResumableError (Handlers s))
getHooks w = do
    contract <- use ctsContract
    evts <- gets (foldMap toList . view (at w) . _ctsEvents)
    return $ State.execResumable evts contract

data ContractTraceResult s a =
    ContractTraceResult
        { _ctrEmulatorState :: EmulatorState
        -- ^ The emulator state at the end of the test
        , _ctrTraceState    :: ContractTraceState s a
        -- ^ Final 'ContractTraceState'
        }

makeLenses ''ContractTraceResult

defaultDist :: InitialDistribution
defaultDist = [(EM.Wallet x, 100) | x <- [1..10]]

-- | Add an event to every wallet's trace
addEventAll :: forall s m a. Monad m => Event s -> ContractTrace s m a ()
addEventAll e = traverse_ (flip addEvent e) allWallets

-- | Run a trace in the emulator and return the
--   final events for each wallet.
execTrace
    :: forall s a.
       Contract s a
    -> ContractTrace s EmulatorAction a ()
    -> Map Wallet [Event s]
execTrace con action =
    let (e, _) = runTrace con action
    in
        either (const Map.empty) (fmap toList . _ctsEvents . snd) e

-- | Run a trace in the emulator and return the final state alongside the
--   result
runTrace
    :: Contract s a
    -> ContractTrace s EmulatorAction a ()
    -> (Either AssertionError ((), ContractTraceState s a), EmulatorState)
runTrace con action =
    withInitialDistribution defaultDist (runStateT action (initState allWallets con))

-- | Run an 'EmulatorAction' on a blockchain with the given initial distribution
--   of funds to wallets.
withInitialDistribution
    :: [(Wallet, Ada)]
    -> EmulatorAction a
    -> (Either AssertionError a, EmulatorState)
withInitialDistribution dist action =
    let s = EM.emulatorStateInitialDist (Map.fromList (first EM.walletPubKey . second Ada.toValue <$> dist))

        -- make sure the wallets know about the initial transaction
        notifyInitial = void (EM.addBlocksAndNotify (fst <$> dist) 1)
    in EM.runEmulator s (EM.processEmulated notifyInitial >> action)

-- | Run a wallet action in the context of the given wallet, notify the wallets,
--   and return the list of new transactions
runWallet
    :: ( MonadEmulator m )
    => Wallet
    -> EM.MockWallet ()
    -> m [Tx]
runWallet w t = do
    tx <- EM.processEmulated $ EM.runWalletActionAndProcessPending allWallets w t
    _ <- EM.processEmulated $ EM.walletsNotifyBlock allWallets tx
    pure tx

-- | Call the endpoint on the contract
callEndpoint
    :: forall l a b s m.
       ( MonadEmulator m
       , KnownSymbol l
       , HasType l a (Input s)
       , AllUniqueLabels (Input s))
    => Wallet
    -> a
    -> ContractTrace s m b ()
callEndpoint w = addEvent w . Endpoint.event @l @_ @s

-- | Balance, sign and submit the unbalanced transaction in the context
--   of the wallet
submitUnbalancedTx
    :: forall a s m.
      ( MonadEmulator m
      , HasType "tx" () (Input s)
      , AllUniqueLabels (Input s)
      )
    => Wallet
    -> UnbalancedTx
    -> ContractTrace s m a [Tx]
submitUnbalancedTx wllt tx =
    addEvent wllt WriteTx.event >> lift (runWallet wllt (Wallet.handleTx tx))

-- | Add the 'LedgerUpdate' event for the given transaction to
--   the traces of all wallets.
addTxEvent
    :: ( MonadEmulator m
       , HasWatchAddress s
       )
    => Tx
    -> ContractTrace s m a ()
addTxEvent tx = do
    idx <- lift (gets (AM.fromUtxoIndex . view EM.index))
    let event = fmap snd $ Map.toList $ WatchAddress.events idx tx
    traverse_ addEventAll event

-- | Get the unbalanced transactions that the wallet's contract instance
--   would like to submit to the blockchain.
unbalancedTransactions
    :: forall s m a.
       ( MonadEmulator m
       , HasType "tx" WriteTx.PendingTransactions (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , AllUniqueLabels (Output s)
       )
    => Wallet
    -> ContractTrace s m a [UnbalancedTx]
unbalancedTransactions w = WriteTx.transactions . either (const mempty) id <$> getHooks w

-- | Get the addresses that are of interest to the wallet's contract instance
interestingAddresses
    :: ( MonadEmulator m
       , HasWatchAddress s
       )
    => Wallet
    -> ContractTrace s m a [Address]
interestingAddresses =
    fmap (Set.toList . WatchAddress.addresses . either (const mempty) id) . getHooks

-- | Add a 'SlotChange' event to the wallet's event trace, informing the
--   contract of the current slot
notifySlot
    :: forall s m a.
       ( MonadEmulator m
       , HasType "slot" Slot (Input s)
       , AllUniqueLabels (Input s)
       )
    => Wallet
    -> ContractTrace s m a ()
notifySlot w = do
    st <- lift $ gets (view (EM.walletStates . at w))
    addEvent w $ AwaitSlot.event (maybe 0 (view EM.walletSlot) st)

-- | Add a number of empty blocks to the blockchain.
addBlocks
    :: ( MonadEmulator m )
    => Integer
    -> ContractTrace s m a ()
addBlocks i =
    void $ lift $ EM.processEmulated (EM.addBlocksAndNotify allWallets i)

-- | Submit the wallet's pending transactions to the blockchain
--   and inform all wallets about new transactions
handleBlockchainEvents
    :: ( MonadEmulator m
       , HasWatchAddress s
       , HasWriteTx s
       )
    => Wallet
    -> ContractTrace s m a ()
handleBlockchainEvents wllt = do
    utxs <- unbalancedTransactions wllt
    traverse_ (submitUnbalancedTx wllt >=> traverse_ addTxEvent) utxs

-- | Notify the wallet of all interesting addresses
notifyInterestingAddresses
    :: ( MonadEmulator m
       , HasWatchAddress s
       )
    => Wallet
    -> ContractTrace s m a ()
notifyInterestingAddresses wllt =
    void $ interestingAddresses wllt >>= lift . runWallet wllt . traverse_ Wallet.startWatching

-- | The wallets used in mockchain simulations by default. There are
--   ten wallets because the emulator comes with ten private keys.
allWallets :: [EM.Wallet]
allWallets = EM.Wallet <$> [1..10]
