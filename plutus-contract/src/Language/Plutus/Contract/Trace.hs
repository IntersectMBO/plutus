{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}
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
import           Control.Monad                         (void)
import           Control.Monad.Reader
import           Control.Monad.State                   (MonadState, StateT, gets, runStateT)
import           Control.Monad.Trans.Class             (MonadTrans (..))
import qualified Data.Aeson                            as Aeson
import           Data.Bifunctor                        (Bifunctor (..))
import           Data.Foldable                         (toList, traverse_)
import           Data.Map                              (Map)
import qualified Data.Map                              as Map
import           Data.Sequence                         (Seq)
import qualified Data.Sequence                         as Seq
import qualified Data.Set                              as Set

import           Language.Plutus.Contract              (Contract, convertContract)
import           Language.Plutus.Contract.Effects      (ContractEffects)
import           Language.Plutus.Contract.Prompt.Event (Event)
import qualified Language.Plutus.Contract.Prompt.Event as Event
import           Language.Plutus.Contract.Prompt.Hooks (Hooks (..))
import qualified Language.Plutus.Contract.Prompt.Hooks as Hooks
import           Language.Plutus.Contract.Resumable    (ResumableError)
import qualified Language.Plutus.Contract.Resumable    as State
import           Language.Plutus.Contract.Tx           (UnbalancedTx)
import qualified Language.Plutus.Contract.Wallet       as Wallet

import           Ledger.Ada                            (Ada)
import qualified Ledger.Ada                            as Ada
import qualified Ledger.AddressMap                     as AM
import           Ledger.Tx                             (Address, Tx)

import           Wallet.Emulator                       (AssertionError, EmulatorAction, EmulatorState, MonadEmulator,
                                                        Wallet)
import qualified Wallet.Emulator                       as EM

type InitialDistribution = [(Wallet, Ada)]

type ContractTrace m a = StateT (ContractTraceState a) m

data ContractTraceState a =
    ContractTraceState
        { _ctsEvents   :: Map Wallet (Seq Event)
        -- ^ The state of the contract instance (per wallet). To get
        --   the 'Record' of a sequence of events, use
        --   'Language.Plutus.Contract.Resumable.runResumable'.
        , _ctsContract :: Contract (ContractEffects '[]) a
        -- ^ Current state of the contract
        }

makeLenses ''ContractTraceState

initState :: [Wallet] -> Contract (ContractEffects '[]) a -> ContractTraceState a
initState wllts = ContractTraceState wallets where
    wallets = Map.fromList $ fmap (,mempty) wllts

-- | Add an event to the wallet's trace
addEvent :: MonadState (ContractTraceState a) m => Wallet -> Event -> m ()
addEvent w e = ctsEvents %= Map.alter go w where
    go = Just . maybe (Seq.singleton e) (|> e)

-- | Get the hooks that a contract is currently waiting for
getHooks :: Monad m => Wallet -> ContractTrace m a (Either ResumableError Hooks)
getHooks w = do
    contract <- use ctsContract
    evts <- gets (foldMap toList . view (at w) . _ctsEvents)
    return $ State.execResumable evts (convertContract contract)

data ContractTraceResult a =
    ContractTraceResult
        { _ctrEmulatorState :: EmulatorState
        -- ^ The emulator state at the end of the test
        , _ctrTraceState    :: ContractTraceState a
        -- ^ Final 'ContractTraceState'
        }

makeLenses ''ContractTraceResult

defaultDist :: InitialDistribution
defaultDist = [(EM.Wallet x, 100) | x <- [1..10]]

-- | Add an event to every wallet's trace
addEventAll :: Monad m => Event -> ContractTrace m a ()
addEventAll e = traverse_ (flip addEvent e) allWallets

-- | Run a trace in the emulator and return the
--   final events for each wallet.
execTrace
    :: Contract (ContractEffects '[]) a
    -> ContractTrace EmulatorAction a ()
    -> Map Wallet [Event]
execTrace con action =
    let (e, _) = runTrace con action
    in
        either (const Map.empty) (fmap toList . _ctsEvents . snd) e

-- | Run a trace in the emulator and return the final state alongside the
--   result
runTrace
    :: Contract (ContractEffects '[]) a
    -> ContractTrace EmulatorAction a ()
    -> (Either AssertionError ((), ContractTraceState a), EmulatorState)
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
    :: ( MonadEmulator m
       , Aeson.ToJSON b )
    => Wallet
    -> String
    -> b
    -> ContractTrace m a ()
callEndpoint w nm = addEvent w . Event.endpoint nm . Aeson.toJSON

-- | Balance, sign and submit the unbalanced transaction in the context
--   of the wallet
submitUnbalancedTx
    :: ( MonadEmulator m )
    => Wallet
    -> UnbalancedTx
    -> ContractTrace m a [Tx]
submitUnbalancedTx wllt tx =
    addEvent wllt Event.txSubmission >> lift (runWallet wllt (Wallet.handleTx tx))

-- | Add the 'LedgerUpdate' event for the given transaction to
--   the traces of all wallets.
addTxEvent
    :: ( MonadEmulator m )
    => Tx
    -> ContractTrace m a ()
addTxEvent tx = do
    idx <- lift (gets (AM.fromUtxoIndex . view EM.index))
    let event = fmap snd $ Map.toList $ Event.txEvents idx tx
    traverse_ addEventAll event

-- | Get the unbalanced transactions that the wallet's contract instance
--   would like to submit to the blockchain.
unbalancedTransactions
    :: ( MonadEmulator m )
    => Wallet
    -> ContractTrace m a [UnbalancedTx]
unbalancedTransactions w = Hooks.transactions . either mempty id <$> getHooks w

-- | Get the addresses that are of interest to the wallet's contract instance
interestingAddresses
    :: ( MonadEmulator m )
    => Wallet
    -> ContractTrace m a [Address]
interestingAddresses =
    fmap (Set.toList . Hooks.addresses . either mempty id) . getHooks

-- | Add a 'SlotChange' event to the wallet's event trace, informing the
--   contract of the current slot
notifySlot
    :: ( MonadEmulator m )
    => Wallet
    -> ContractTrace m a ()
notifySlot w = do
    st <- lift $ gets (view (EM.walletStates . at w))
    addEvent w $ Event.changeSlot (maybe 0 (view EM.walletSlot) st)

-- | Add a number of empty blocks to the blockchain.
addBlocks
    :: ( MonadEmulator m )
    => Integer
    -> ContractTrace m a ()
addBlocks i =
    void $ lift $ EM.processEmulated (EM.addBlocksAndNotify allWallets i)

-- | Submit the wallet's pending transactions to the blockchain
--   and inform all wallets about new transactions
handleBlockchainEvents
    :: ( MonadEmulator m )
    => Wallet
    -> ContractTrace m a ()
handleBlockchainEvents wllt = do
    utxs <- unbalancedTransactions wllt
    traverse_ (submitUnbalancedTx wllt >=> traverse_ addTxEvent) utxs

-- | Notify the wallet of all interesting addresses
notifyInterestingAddresses
    :: ( MonadEmulator m )
    => Wallet
    -> ContractTrace m a ()
notifyInterestingAddresses wllt =
    void $ interestingAddresses wllt >>= lift . runWallet wllt . traverse_ Wallet.startWatching

-- | The wallets used in mockchain simulations by default. There are
--   ten wallets because the emulator comes with ten private keys.
allWallets :: [EM.Wallet]
allWallets = EM.Wallet <$> [1..10]
