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
    , handleUtxoQueries
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

import           Language.Plutus.Contract                        (Contract (..), HasUtxoAt, HasWatchAddress, HasWriteTx,
                                                                  waitingForBlockchainActions)
import           Language.Plutus.Contract.Resumable              (ResumableError)
import qualified Language.Plutus.Contract.Resumable              as State
import           Language.Plutus.Contract.Schema                 (Event, Handlers, Input, Output)
import           Language.Plutus.Contract.Tx                     (UnbalancedTx)
import qualified Language.Plutus.Contract.Wallet                 as Wallet

import           Language.Plutus.Contract.Effects.AwaitSlot      (SlotSymbol)
import qualified Language.Plutus.Contract.Effects.AwaitSlot      as AwaitSlot
import           Language.Plutus.Contract.Effects.ExposeEndpoint (HasEndpoint)
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoint
import           Language.Plutus.Contract.Effects.UtxoAt         (UtxoAtAddress (..))
import qualified Language.Plutus.Contract.Effects.UtxoAt         as UtxoAt
import qualified Language.Plutus.Contract.Effects.WatchAddress   as WatchAddress
import           Language.Plutus.Contract.Effects.WriteTx        (TxSymbol, WriteTxResponse)
import qualified Language.Plutus.Contract.Effects.WriteTx        as WriteTx

import           Ledger.Ada                                      (Ada)
import qualified Ledger.Ada                                      as Ada
import qualified Ledger.AddressMap                               as AM
import           Ledger.Slot                                     (Slot)
import           Ledger.Tx                                       (Address, Tx, hashTx)

import           Wallet.API                                      (WalletAPIError)
import           Wallet.Emulator                                 (EmulatorAction, EmulatorState, MonadEmulator, Wallet)
import qualified Wallet.Emulator                                 as EM

type InitialDistribution = [(Wallet, Ada)]

type ContractTrace s e m a = StateT (ContractTraceState s e a) m

data ContractTraceState s e a =
    ContractTraceState
        { _ctsEvents   :: Map Wallet (Seq (Event s))
        -- ^ The state of the contract instance (per wallet). To get
        --   the 'Record' of a sequence of events, use
        --   'Language.Plutus.Contract.Resumable.runResumable'.
        , _ctsContract :: Contract s e a
        -- ^ Current state of the contract
        }

makeLenses ''ContractTraceState

initState
    :: [Wallet]
    -> Contract s e a
    -> ContractTraceState s e a
initState wllts = ContractTraceState wallets where
    wallets = Map.fromList $ fmap (,mempty) wllts

-- | Add an event to the wallet's trace
addEvent :: forall s e m a. MonadState (ContractTraceState s e a) m => Wallet -> Event s -> m ()
addEvent w e = ctsEvents %= Map.alter go w where
    go = Just . maybe (Seq.singleton e) (|> e)

-- | Get the hooks that a contract is currently waiting for
getHooks
    :: forall s e m a.
       ( Monad m
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , AllUniqueLabels (Output s)
       )
    => Wallet
    -> ContractTrace s e m a (Either (ResumableError e) (Handlers s))
getHooks w = do
    contract <- unContract <$> use ctsContract
    evts <- gets (foldMap toList . view (at w) . _ctsEvents)
    return $ State.execResumable evts contract

data ContractTraceResult s e a =
    ContractTraceResult
        { _ctrEmulatorState :: EmulatorState
        -- ^ The emulator state at the end of the test
        , _ctrTraceState    :: ContractTraceState s e a
        -- ^ Final 'ContractTraceState'
        }

makeLenses ''ContractTraceResult

defaultDist :: InitialDistribution
defaultDist = [(EM.Wallet x, 100) | x <- [1..10]]

-- | Add an event to every wallet's trace
addEventAll :: forall s e m a. Monad m => Event s -> ContractTrace s e m a ()
addEventAll e = traverse_ (flip addEvent e) allWallets

-- | Run a trace in the emulator and return the
--   final events for each wallet.
execTrace
    :: forall s e a
    . EM.AsAssertionError e
    => Contract s e a
    -> ContractTrace s e (EmulatorAction e) a ()
    -> Map Wallet [Event s]
execTrace con action =
    let (e, _) = runTrace con action
    in
        either (const Map.empty) (fmap toList . _ctsEvents . snd) e

-- | Run a trace in the emulator and return the final state alongside the
--   result
runTrace
    :: EM.AsAssertionError e
    => Contract s e a
    -> ContractTrace s e (EmulatorAction e) a ()
    -> (Either e ((), ContractTraceState s e a), EmulatorState)
runTrace con action =
    withInitialDistribution defaultDist (runStateT action (initState allWallets con))

-- | Run an 'EmulatorAction' on a blockchain with the given initial distribution
--   of funds to wallets.
withInitialDistribution
    :: EM.AsAssertionError e
    => [(Wallet, Ada)]
    -> EmulatorAction e a
    -> (Either e a, EmulatorState)
withInitialDistribution dist action =
    let s = EM.emulatorStateInitialDist (Map.fromList (first EM.walletPubKey . second Ada.toValue <$> dist))

        -- make sure the wallets know about the initial transaction
        notifyInitial = void (EM.addBlocksAndNotify (fst <$> dist) 1)
    in EM.runEmulator s (EM.processEmulated notifyInitial >> action)

-- | Run a wallet action in the context of the given wallet, notify the wallets,
--   and return the list of new transactions
runWallet
    :: ( MonadEmulator e m )
    => Wallet
    -> EM.MockWallet a
    -> m ([Tx], Either WalletAPIError a)
runWallet w t = do
    (tx, result) <- EM.processEmulated $ EM.runWalletActionAndProcessPending allWallets w t
    _ <- EM.processEmulated $ EM.walletsNotifyBlock allWallets tx
    pure (tx, result)

-- | Call the endpoint on the contract
callEndpoint
    :: forall l ep s e m a.
       ( MonadEmulator e m
       , HasEndpoint l ep s
       )
    => Wallet
    -> ep
    -> ContractTrace s e m a ()
callEndpoint w = addEvent w . Endpoint.event @l @_ @s

-- | Balance, sign and submit the unbalanced transaction in the context
--   of the wallet
submitUnbalancedTx
    :: forall s e m a.
      ( MonadEmulator e m
      , HasType TxSymbol WriteTxResponse (Input s)
      , AllUniqueLabels (Input s)
      )
    => Wallet
    -> UnbalancedTx
    -> ContractTrace s e m a [Tx]
submitUnbalancedTx wllt tx = do
    (txns, res) <- lift (runWallet wllt (Wallet.handleTx tx))
    addEvent wllt (WriteTx.event $ view (from WriteTx.writeTxResponse) $ fmap hashTx res)
    pure txns

addInterestingTxEvents
    :: forall s e m a.
       ( HasWatchAddress s
       , MonadEmulator e m
       )
    => Map Address (Event s)
    -> Wallet
    -> ContractTrace s e m a ()
addInterestingTxEvents mp wallet = do
    hks <- fmap (either (const mempty) id) (getHooks wallet)
    let relevantAddresses = WatchAddress.addresses hks
        relevantTransactions =
            fmap snd
            $ Map.toList
            $ Map.filterWithKey (\addr _ -> addr `Set.member` relevantAddresses) mp
    traverse_ (addEvent wallet) relevantTransactions

-- | Respond to all 'WatchAddress' requests from contracts that are waiting
--   for a change to an address touched by this transaction
addTxEvents
    :: ( MonadEmulator e m
       , HasWatchAddress s
       )
    => Tx
    -> ContractTrace s e m a ()
addTxEvents tx = do
    idx <- lift (gets (AM.fromUtxoIndex . view EM.index))
    let events = WatchAddress.events idx tx
    traverse_ (addInterestingTxEvents events) allWallets

-- | Get the unbalanced transactions that the wallet's contract instance
--   would like to submit to the blockchain.
unbalancedTransactions
    :: forall s e m a.
       ( Monad m
       , HasType TxSymbol WriteTx.PendingTransactions (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , AllUniqueLabels (Output s)
       )
    => Wallet
    -> ContractTrace s e m a [UnbalancedTx]
unbalancedTransactions w = WriteTx.transactions . either (const mempty) id <$> getHooks w

-- | Get the address that the contract has requested the unspent outputs for.
utxoQueryAddresses
    :: forall s e m a.
       ( MonadEmulator e m
       , HasUtxoAt s
       )
    => Wallet
    -> ContractTrace s e m a (Set.Set Address)
utxoQueryAddresses =
    fmap (UtxoAt.addresses . either (const mempty) id) . getHooks

-- | Get the addresses that are of interest to the wallet's contract instance
interestingAddresses
    :: ( MonadEmulator e m
       , HasWatchAddress s
       )
    => Wallet
    -> ContractTrace s e m a [Address]
interestingAddresses =
    fmap (Set.toList . WatchAddress.addresses . either (const mempty) id) . getHooks

-- | Add a 'SlotChange' event to the wallet's event trace, informing the
--   contract of the current slot
notifySlot
    :: forall s e m a.
       ( MonadEmulator e m
       , HasType SlotSymbol Slot (Input s)
       , AllUniqueLabels (Input s)
       )
    => Wallet
    -> ContractTrace s e m a ()
notifySlot w = do
    st <- lift $ gets (view (EM.walletStates . at w))
    addEvent w $ AwaitSlot.event (maybe 0 (view EM.walletSlot) st)

-- | Add a number of empty blocks to the blockchain.
addBlocks
    :: ( MonadEmulator e m )
    => Integer
    -> ContractTrace s e m a ()
addBlocks i =
    void $ lift $ EM.processEmulated (EM.addBlocksAndNotify allWallets i)

handleBlockchainEvents
    :: ( MonadEmulator e m
       , HasUtxoAt s
       , HasWatchAddress s
       , HasWriteTx s
       )
    => Wallet
    -> ContractTrace s e m a ()
handleBlockchainEvents wallet = do
    hks <- fmap (either (const mempty) id) (getHooks wallet)
    if waitingForBlockchainActions hks
    then do
        submitUnbalancedTxns wallet
        handleUtxoQueries wallet
        handleBlockchainEvents wallet
    else pure ()

-- | Submit the wallet's pending transactions to the blockchain
--   and inform all wallets about new transactions and respond to
--   UTXO queries
submitUnbalancedTxns
    :: ( MonadEmulator e m
       , HasWatchAddress s
       , HasWriteTx s
       )
    => Wallet
    -> ContractTrace s e m a ()
submitUnbalancedTxns wllt = do
    utxs <- unbalancedTransactions wllt
    traverse_ (submitUnbalancedTx wllt >=> traverse_ addTxEvents) utxs

-- | Look at the "utxo-at" requests of the contract and respond to all of them
--   with the current UTXO set at the given address.
handleUtxoQueries
    :: ( MonadEmulator e m
       , HasUtxoAt s
       )
    => Wallet
    -> ContractTrace s e m a ()
handleUtxoQueries wllt = do
    addresses <- utxoQueryAddresses wllt
    AM.AddressMap utxoSet <- lift (gets (flip AM.restrict addresses . AM.fromUtxoIndex . view EM.index))
    let events = fmap snd $ Map.toList $ Map.mapWithKey UtxoAtAddress utxoSet
    traverse_ (addEvent wllt . UtxoAt.event) events

-- | Notify the wallet of all interesting addresses
notifyInterestingAddresses
    :: ( MonadEmulator e m
       , HasWatchAddress s
       )
    => Wallet
    -> ContractTrace s e m a ()
notifyInterestingAddresses wllt =
    void $ interestingAddresses wllt >>= lift . runWallet wllt . traverse_ Wallet.startWatching

-- | The wallets used in mockchain simulations by default. There are
--   ten wallets because the emulator comes with ten private keys.
allWallets :: [EM.Wallet]
allWallets = EM.Wallet <$> [1..10]
