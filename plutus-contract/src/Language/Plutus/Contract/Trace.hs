{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MonoLocalBinds         #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
-- | A trace is a sequence of actions by simulated wallets that can be run
--   on the mockchain. This module contains the functions needed to build
--   traces.
module Language.Plutus.Contract.Trace
    ( ContractTraceState
    , ContractTrace
    , EmulatorAction
    , TraceError(..)
    , AsTraceError(..)
    , WalletState(..)
    , ctsWalletStates
    , ctsContract
    , eventsByWallet
    , handlersByWallet
    , checkpointStoreByWallet
    , ContractTraceResult(..)
    , ctrEmulatorState
    , ctrTraceState
    , runTrace
    , runTraceWithDistribution
    , evalTrace
    , execTrace
    , setSigningProcess
    -- * Constructing 'MonadEmulator' actions
    , runWallet
    , getHooks
    , callEndpoint
    , handleUtxoQueries
    , addBlocks
    , addBlocksUntil
    , addEvent
    , addNamedEvent
    , addResponse
    , notifyInterestingAddresses
    , notifySlot
    , payToWallet
    -- * Handle blockchain events repeatedly
    , MaxIterations(..)
    , handleBlockchainEvents
    , handleBlockchainEventsTimeout
    -- * Running 'MonadEmulator' actions
    , MonadEmulator
    , InitialDistribution
    , withInitialDistribution
    , defaultDist
    -- * Wallets
    , EM.Wallet(..)
    , EM.walletPubKey
    , EM.walletPrivKey
    , allWallets
    ) where

import           Control.Lens                                      (at, from, makeClassyPrisms, makeLenses, non, use,
                                                                    view, (%=))
import           Control.Monad.Except
import qualified Control.Monad.Freer                               as Eff
import qualified Control.Monad.Freer.Error                         as Eff
import           Control.Monad.Reader                              ()
import           Control.Monad.State                               (MonadState, StateT, gets, runStateT)
import           Data.Bifunctor                                    (Bifunctor (..))
import           Data.Foldable                                     (toList, traverse_)
import           Data.Map                                          (Map)
import qualified Data.Map                                          as Map
import           Data.Maybe                                        (fromMaybe, mapMaybe)
import           Data.Row                                          (AllUniqueLabels, HasType, KnownSymbol, Label (..),
                                                                    trial')
import qualified Data.Row.Internal                                 as V
import qualified Data.Row.Variants                                 as V
import           Data.Sequence                                     (Seq, (|>))
import qualified Data.Set                                          as Set
import           Data.Text                                         (Text)
import qualified Data.Text                                         as Text
import           Data.Text.Extras                                  (tshow)
import           Numeric.Natural                                   (Natural)

import           Language.Plutus.Contract                          (Contract (..), HasAwaitSlot, HasTxConfirmation,
                                                                    HasUtxoAt, HasWatchAddress, HasWriteTx, mapError,
                                                                    waitingForBlockchainActions)
import           Language.Plutus.Contract.Checkpoint               (CheckpointStore)
import qualified Language.Plutus.Contract.Resumable                as State
import           Language.Plutus.Contract.Schema                   (Event (..), Handlers (..), Input, Output)
import qualified Language.Plutus.Contract.Types                    as Contract.Types
import qualified Language.Plutus.Contract.Wallet                   as Wallet

import qualified Language.Plutus.Contract.Effects.AwaitSlot        as AwaitSlot
import qualified Language.Plutus.Contract.Effects.AwaitTxConfirmed as AwaitTxConfirmed
import           Language.Plutus.Contract.Effects.ExposeEndpoint   (HasEndpoint)
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint   as Endpoint
import           Language.Plutus.Contract.Effects.OwnPubKey        (HasOwnPubKey)
import qualified Language.Plutus.Contract.Effects.OwnPubKey        as OwnPubKey
import           Language.Plutus.Contract.Effects.UtxoAt           (UtxoAtAddress (..))
import qualified Language.Plutus.Contract.Effects.UtxoAt           as UtxoAt
import qualified Language.Plutus.Contract.Effects.WatchAddress     as WatchAddress
import           Language.Plutus.Contract.Effects.WriteTx          (TxSymbol, WriteTxResponse)
import qualified Language.Plutus.Contract.Effects.WriteTx          as WriteTx
import           Language.Plutus.Contract.Resumable                (Request (..), Requests (..), Response (..))
import           Language.Plutus.Contract.Types                    (ResumableResult (..))

import qualified Ledger.Ada                                        as Ada
import           Ledger.Address                                    (Address)
import qualified Ledger.AddressMap                                 as AM
import           Ledger.Constraints.OffChain                       (UnbalancedTx)
import           Ledger.Slot                                       (Slot (..))
import           Ledger.Tx                                         (Tx, txId)
import           Ledger.TxId                                       (TxId)
import           Ledger.Value                                      (Value)

import           Wallet.API                                        (defaultSlotRange, payToPublicKey_)
import           Wallet.Emulator                                   (EmulatorAction, EmulatorState, MonadEmulator,
                                                                    Wallet)
import qualified Wallet.Emulator                                   as EM
import qualified Wallet.Emulator.MultiAgent                        as EM
import qualified Wallet.Emulator.NodeClient                        as EM
import           Wallet.Emulator.SigningProcess                    (SigningProcess)
import qualified Wallet.Emulator.SigningProcess                    as EM

-- | Maximum number of iterations of `handleBlockchainEvents`.
newtype MaxIterations = MaxIterations Natural
    deriving (Eq, Ord, Show)

-- | The default for 'MaxIterations' is twenty.
defaultMaxIterations :: MaxIterations
defaultMaxIterations = MaxIterations 20

-- | Error produced while running a trace. Either a contract-specific
--   error (of type 'e'), or an 'EM.AssertionError' from the emulator.
data TraceError e =
    TraceAssertionError EM.AssertionError
    | TContractError e
    | HandleBlockchainEventsMaxIterationsExceeded MaxIterations
    | HookError Text
    deriving (Eq, Show)

type InitialDistribution = Map Wallet Value

type ContractTrace s e m a = StateT (ContractTraceState s (TraceError e) a) m

data WalletState s e a =
    WalletState
        { walletContractState   :: Either e (ResumableResult (Event s) (Handlers s) a)
        , walletEvents          :: Seq (Response (Event s))
        , walletHandlersHistory :: Seq [State.Request (Handlers s)]
        }

walletHandlers :: WalletState s (TraceError e) a -> [State.Request (Handlers s)]
walletHandlers = either mempty (State.unRequests . wcsRequests) . walletContractState

emptyWalletState :: Contract s e a -> WalletState s e a
emptyWalletState (Contract c) =
    WalletState
        { walletContractState = Contract.Types.runResumable [] mempty c
        , walletEvents = mempty
        , walletHandlersHistory = mempty
        }

addEventWalletState ::
    Contract s e a
    -> Response (Event s)
    -> WalletState s e a
    -> WalletState s e a
addEventWalletState (Contract c) event s@WalletState{walletContractState, walletEvents, walletHandlersHistory} =
    case walletContractState of
        Left _ -> s
        Right ResumableResult{wcsResponses,wcsRequests=Requests{unRequests},wcsCheckpointStore} ->
            let state' = Contract.Types.insertAndUpdate c wcsCheckpointStore wcsResponses event
                events' = walletEvents |> event
                history' = walletHandlersHistory |> unRequests
            in s { walletContractState = state', walletEvents = events', walletHandlersHistory = history'}

data ContractTraceState s e a =
    ContractTraceState
        { _ctsWalletStates :: Map Wallet (WalletState s e a)
        -- ^ The state of the contract instance (per wallet). To get
        --   the 'Record' of a sequence of events, use
        --   'Language.Plutus.Contract.Resumable.runResumable'.
        , _ctsContract     :: Contract s e a
        -- ^ Current state of the contract
        }

eventsByWallet :: ContractTraceState s e a -> Map Wallet [Response (Event s)]
eventsByWallet = fmap (toList . walletEvents) . _ctsWalletStates

handlersByWallet :: ContractTraceState s e a -> Map Wallet [[State.Request (Handlers s)]]
handlersByWallet = fmap (toList . walletHandlersHistory) . _ctsWalletStates

checkpointStoreByWallet :: ContractTraceState s e a -> Map Wallet CheckpointStore
checkpointStoreByWallet = fmap (either (const mempty) wcsCheckpointStore . walletContractState) . _ctsWalletStates

makeLenses ''ContractTraceState

initState ::
    [Wallet]
    -> Contract s e a
    -> ContractTraceState s e a
initState wllts con = ContractTraceState wallets con where
    wallets = Map.fromList $ fmap (\a -> (a,emptyWalletState con)) wllts

-- | Add an event to the wallet's trace
addEvent ::
    forall l s e m a.
    ( MonadEmulator (TraceError e) m
    , KnownSymbol l
    )
    => Wallet
    -> Event s
    -> ContractTrace s e m a ()
addEvent wallet event = do
    let filterReq Request{rqID, itID, rqRequest=Handlers v} = do
            _ <- trial' v (Label @l)
            Just Response{rspRqID=rqID, rspItID=itID, rspResponse=event}
    hks <- mapMaybe filterReq <$> getHooks wallet >>= \case
            [] -> throwError $ HookError $ "No hooks found for " <> tshow (Label @l)
            [x] -> pure x
            _ -> throwError $ HookError $ "More than one hook found for " <> tshow (Label @l)
    addResponse wallet hks

-- | A variant of 'addEvent' that takes the name of the endpoint as a value
--   instead of a type argument. This is useful for the playground where we
--   don't have the type-level symbol of user-defined endpoint calls.
--   Unfortunately this requires the 'V.Forall (Output s) V.Unconstrained1'
--   constraint. Luckily 'V.Forall (Output s) V.Unconstrained1' holds for all
--   schemas, so it doesn't restrict the callers of 'addNamedEvent'. But we
--   have to propagate it up to the top level :(
addNamedEvent ::
    forall s e m a.
    ( MonadEmulator (TraceError e) m
    --   TODO: remove (using 'constraints' package)
    , V.Forall (Output s) V.Unconstrained1
    )
    => String -- endpoint name
    -> Wallet
    -> Event s
    -> ContractTrace s e m a ()
addNamedEvent endpointName wallet event = do
    let filterReq Request{rqID, itID, rqRequest=Handlers v} = do
            guard $
                (V.eraseWithLabels @V.Unconstrained1 (const ()) v)
                    == (endpointName, ())
            Just Response{rspRqID=rqID, rspItID=itID, rspResponse=event}
    hks <- mapMaybe filterReq <$> getHooks wallet >>= \case
            [] -> throwError $ HookError $ "No hooks found for " <> Text.pack endpointName
            [x] -> pure x
            _ -> throwError $ HookError $ "More than one hook found for " <> Text.pack endpointName
    addResponse wallet hks


-- | Add a 'Response' to the wallet's trace
addResponse
    :: forall s e m a.
       ( MonadState (ContractTraceState s e a) m
       )
    => Wallet
    -> Response (Event s)
    -> m ()
addResponse w e = do
    con <- use ctsContract
    let go st =
            let theState = fromMaybe (emptyWalletState con) st
             in Just (addEventWalletState con e theState)
    ctsWalletStates %= Map.alter go w

-- | Get the hooks that a contract is currently waiting for
getHooks
    :: forall s e m a.
       ( Monad m
       )
    => Wallet
    -> ContractTrace s e m a [Request (Handlers s)]
getHooks w =
    foldMap walletHandlers . Map.lookup w <$> use ctsWalletStates

data ContractTraceResult s e a =
    ContractTraceResult
        { _ctrEmulatorState :: EmulatorState
        -- ^ The emulator state at the end of the test
        , _ctrTraceState    :: ContractTraceState s e a
        -- ^ Final 'ContractTraceState'
        }

makeLenses ''ContractTraceResult

-- | Set the wallet's 'SigningProcess' to a new value.
setSigningProcess
    :: forall s e m a.
       ( MonadEmulator (TraceError e) m )
    => Wallet
    -> SigningProcess
    -> ContractTrace s e m a ()
setSigningProcess wallet signingProcess =
    void $ lift $ runWalletControl wallet (EM.setSigningProcess signingProcess)

-- | Run a trace in the emulator and return the
--   final events for each wallet.
execTrace
    :: forall s e a.
    Contract s e a
    -> ContractTrace s e (EmulatorAction (TraceError e)) a ()
    -> Map Wallet [Response (Event s)]
execTrace con action =
    let (e, _) = runTrace con action
    in
        either (const Map.empty) (fmap (toList . walletEvents) . _ctsWalletStates . snd) e

-- | Run a trace in the emulator and return the final state alongside the
--   result
runTrace ::
    Contract s e a
    -> ContractTrace s e (EmulatorAction (TraceError e)) a ()
    -> (Either (TraceError e) ((), ContractTraceState s (TraceError e) a), EmulatorState)
runTrace = runTraceWithDistribution defaultDist

-- | Run a contract and return the result for the given wallet, if it exists
evalTrace ::
    forall s e a.
    Contract s e a
    -> ContractTrace s e (EmulatorAction (TraceError e)) a ()
    -> Wallet
    -> Either String a
evalTrace contract trace wllt = do
    (_, state) <- first (const "contract trace failed") $ fst $ runTrace @s @e contract trace
    wlltState <- maybe (Left "wallet state not found") pure $ view (ctsWalletStates . at wllt) state
    ResumableResult{wcsFinalState} <- first (const $ "contract failed for wallet " <> show wllt) (walletContractState wlltState)
    maybe (Left "contract not finished") pure wcsFinalState

-- | Run a trace in the emulator and return the final state alongside the
--   result
runTraceWithDistribution ::
    InitialDistribution
    -> Contract s e a
    -> ContractTrace s e (EmulatorAction (TraceError e)) a ()
    -> (Either (TraceError e) ((), ContractTraceState s (TraceError e) a), EmulatorState)
runTraceWithDistribution dist con action =
  let con' = mapError TContractError con in
  withInitialDistribution dist (runStateT action (initState (Map.keys dist) con'))

-- | Run an 'EmulatorAction' on a blockchain with the given initial distribution
--   of funds to wallets.
withInitialDistribution ::
       EM.AsAssertionError e
    => InitialDistribution
    -> EmulatorAction e a
    -> (Either e a, EmulatorState)
withInitialDistribution dist action =
    let s = EM.emulatorStateInitialDist (Map.mapKeys EM.walletPubKey dist)
        -- make sure the wallets know about the initial transaction
        notifyInitial = void (EM.addBlocksAndNotify (Map.keys dist) 1)
     in EM.runEmulator s (EM.processEmulated notifyInitial >> action)

-- | Run a wallet action in the context of the given wallet, notify the wallets,
--   and return the list of new transactions
runWallet
    :: ( MonadEmulator (TraceError e) m )
    => Wallet
    -> Eff.Eff EM.EmulatedWalletEffects a
    -> m ([Tx], a)
runWallet w t = do
    (tx, result) <- EM.processEmulated $ EM.runWalletActionAndProcessPending allWallets w t
    _ <- EM.processEmulated $ EM.walletsNotifyBlock allWallets tx
    pure (tx, result)

runWalletControl
    :: ( MonadEmulator (TraceError e) m )
    => Wallet
    -> Eff.Eff EM.EmulatedWalletControlEffects a
    -> m ([Tx], a)
runWalletControl w t = do
    (tx, result) <- EM.processEmulated $ EM.runWalletControlActionAndProcessPending allWallets w t
    _ <- EM.processEmulated $ EM.walletsNotifyBlock allWallets tx
    pure (tx, result)

-- | Call the endpoint on the contract
callEndpoint
    :: forall l ep s e m a.
       ( MonadEmulator (TraceError e) m
       , HasEndpoint l ep s
       )
    => Wallet
    -> ep
    -> ContractTrace s e m a ()
callEndpoint wallet ep = do
    -- check if the endpoint is active and throw an error if it isn't
    hks <- getHooks wallet
    unless (any (Endpoint.isActive @l) $ fmap rqRequest hks) $
        throwError $ HookError $ "Endpoint " <> tshow (Label @l) <> " not active on " <> tshow wallet

    let handleEvent e
            | Endpoint.isActive @l e = Just (Endpoint.event @l ep)
            | otherwise = Nothing

    respondToRequest wallet handleEvent

-- | Balance, sign and submit the unbalanced transaction in the context
--   of the wallet
submitUnbalancedTx
    :: forall s e m a.
       ( MonadEmulator (TraceError e) m
       , HasType TxSymbol WriteTxResponse (Input s)
       , AllUniqueLabels (Input s)
       )
    => Wallet
    -> UnbalancedTx
    -> ContractTrace s e m a [Tx]
submitUnbalancedTx wallet tx = do
    (txns, res) <- lift (runWallet wallet ((Right <$> Wallet.handleTx tx) `Eff.catchError` \e -> pure $ Left e))
    let event = WriteTx.event $ view (from WriteTx.writeTxResponse) $ fmap txId res
    addEvent @TxSymbol wallet event
    pure  txns

-- | Inspect the open requests of a wallet's contract instance,
--   and maybe respond to them.
respondToRequest ::
    forall s e m a.
    ( MonadEmulator (TraceError e) m
    )
    => Wallet
    -- ^ The wallet
    -> (Handlers s -> Maybe (Event s))
    -- ^ How to respond to the requests. If this returns 'Just' for more than
    --   one request then only the first response will be submitted to the
    --   contract
    -> ContractTrace s e m a ()
respondToRequest wallet f = do
    hks <- getHooks wallet
    let -- pick the first request that matches the predicate f
        relevantRequest = msum (fmap (traverse f) hks)
        handleReq Request{rqID,itID,rqRequest} =
           addResponse wallet Response{rspItID=itID, rspRqID=rqID, rspResponse=rqRequest}
    traverse_ handleReq relevantRequest

addInterestingTxEvents
    :: forall s e m a.
       ( HasWatchAddress s
       , MonadEmulator (TraceError e) m
       )
    => Map Address (Event s)
    -> Wallet
    -> ContractTrace s e m a ()
addInterestingTxEvents mp wallet =
    let handleEvent = WatchAddress.watchedAddress >=> flip Map.lookup mp
    in respondToRequest wallet handleEvent

addTxConfirmedEvent
    :: forall s e m a.
        ( HasTxConfirmation s
        , MonadEmulator (TraceError e) m
        )
    => TxId
    -> Wallet
    -> ContractTrace s e m a ()
addTxConfirmedEvent txid wallet =
    let handleEvent e = case AwaitTxConfirmed.txId e of
            Just txid' | txid' == txid -> Just (AwaitTxConfirmed.event txid)
            _                          -> Nothing
    in respondToRequest wallet handleEvent

-- | Respond to all 'WatchAddress' requests from contracts that are waiting
--   for a change to an address touched by this transaction
addTxEvents
    :: ( MonadEmulator (TraceError e) m
       , HasWatchAddress s
       , HasTxConfirmation s
       )
    => Tx
    -> ContractTrace s e m a ()
addTxEvents tx = do
    let addTxEventsWallet wllt = do
            idx <- lift (gets (view (EM.walletClientState wllt . EM.clientIndex)))
            let watchAddressEvents = WatchAddress.events idx tx
            addInterestingTxEvents watchAddressEvents wllt
            addTxConfirmedEvent (txId tx) wllt
    traverse_ addTxEventsWallet allWallets

-- | Get the unbalanced transactions that the wallet's contract instance
--   would like to submit to the blockchain.
unbalancedTransactions
    :: forall s e m a.
       ( Monad m
       , HasType TxSymbol UnbalancedTx (Output s)
       )
    => Wallet
    -> ContractTrace s e m a [UnbalancedTx]
unbalancedTransactions wllt =
    mapMaybe (WriteTx.pendingTransaction . rqRequest) <$> getHooks wllt

-- | Get the address that the contract has requested the unspent outputs for.
utxoQueryAddresses
    :: forall s e m a.
       ( MonadEmulator (TraceError e) m
       , HasUtxoAt s
       )
    => Wallet
    -> ContractTrace s e m a (Set.Set Address)
utxoQueryAddresses wllt =
    Set.fromList . mapMaybe (UtxoAt.utxoAtRequest . rqRequest) <$> getHooks wllt

-- | Get the addresses that are of interest to the wallet's contract instance
interestingAddresses
    :: ( MonadEmulator (TraceError e) m
       , HasWatchAddress s
       )
    => Wallet
    -> ContractTrace s e m a [Address]
interestingAddresses wllt =
    mapMaybe (WatchAddress.watchedAddress . rqRequest) <$> getHooks wllt

-- | Add a 'SlotChange' event to the wallet's event trace, informing the
--   contract of the current slot
notifySlot
    :: forall s e m a.
       ( MonadEmulator (TraceError e) m
       , HasAwaitSlot s
       )
    => Wallet
    -> ContractTrace s e m a ()
notifySlot wallet = do
    currentSlot <- lift $ gets (view (EM.walletClientStates . at wallet . non EM.emptyNodeClientState . EM.clientSlot))
    let handleEvent e = case AwaitSlot.nextSlot e of
            Just slot | slot <= currentSlot -> Just (AwaitSlot.event currentSlot)
            _                               -> Nothing
    respondToRequest wallet handleEvent

-- | Add a number of empty blocks to the blockchain.
addBlocks
    :: ( MonadEmulator (TraceError e) m )
    => Integer
    -> ContractTrace s e m a ()
addBlocks i =
    void $ lift $ EM.processEmulated (EM.addBlocksAndNotify allWallets i)

-- | Add blocks until the given slot has been reached.
addBlocksUntil
    :: ( MonadEmulator (TraceError e) m )
    => Slot
    -> ContractTrace s e m a ()
addBlocksUntil sl = do
    currentSlot <- lift $ use (EM.chainState . EM.currentSlot)
    let Slot missing = sl - currentSlot
    addBlocks (max 0 missing)

-- | Handle all blockchain events for the wallet, throwing an error
--   if there are unhandled events after 'defaultMaxIterations'.
handleBlockchainEvents
    :: ( MonadEmulator (TraceError e) m
       , HasUtxoAt s
       , HasWatchAddress s
       , HasWriteTx s
       , HasOwnPubKey s
       , HasTxConfirmation s
       )
    => Wallet
    -> ContractTrace s e m a ()
handleBlockchainEvents = handleBlockchainEventsTimeout defaultMaxIterations

-- | Handle all blockchain events for the wallet, throwing an error
--   if the given number of iterations is exceeded
handleBlockchainEventsTimeout
    :: ( MonadEmulator (TraceError e) m
    , HasUtxoAt s
    , HasWatchAddress s
    , HasWriteTx s
    , HasOwnPubKey s
    , HasTxConfirmation s
    )
    => MaxIterations
    -> Wallet
    -> ContractTrace s e m a ()
handleBlockchainEventsTimeout (MaxIterations i) wallet = go 0 where
    go j | j >= i    = lift (throwError (HandleBlockchainEventsMaxIterationsExceeded (MaxIterations i)))
         | otherwise = do
            hks <- getHooks wallet
            if any (waitingForBlockchainActions . rqRequest) hks
                then do
                    submitPendingTransactions wallet
                    handleUtxoQueries wallet
                    handleOwnPubKeyQueries wallet
                    go (j + 1)
                else pure ()

-- | Submit the wallet's pending transactions to the blockchain
--   and inform all wallets about new transactions and respond to
--   UTXO queries
submitPendingTransactions
    :: ( MonadEmulator (TraceError e) m
       , HasWatchAddress s
       , HasWriteTx s
       , HasTxConfirmation s
       )
    => Wallet
    -> ContractTrace s e m a ()
submitPendingTransactions wllt = do
    utxs <- unbalancedTransactions wllt
    traverse_ (submitUnbalancedTx wllt >=> traverse_ addTxEvents) utxs

-- | Look at the "utxo-at" requests of the contract and respond to all of them
--   with the current UTXO set at the given address.
handleUtxoQueries
    :: ( MonadEmulator (TraceError e) m
       , HasUtxoAt s
       )
    => Wallet
    -> ContractTrace s e m a ()
handleUtxoQueries wallet = do
    addresses <- utxoQueryAddresses wallet
    AM.AddressMap utxoSet <- lift (gets (flip AM.restrict addresses . view (EM.walletClientState wallet . EM.clientIndex)))
    let handleEvent e = case UtxoAt.utxoAtRequest e of
            Just addr -> fmap (UtxoAt.event . UtxoAtAddress addr) (Map.lookup addr utxoSet)
            _         -> Nothing
    respondToRequest wallet handleEvent

handleOwnPubKeyQueries
    :: ( MonadEmulator (TraceError e) m
       , HasOwnPubKey s
       )
    => Wallet
    -> ContractTrace s e m a ()
handleOwnPubKeyQueries wallet =
    let handleEvent e = case OwnPubKey.request e of
            Just _ -> pure (OwnPubKey.event (EM.walletPubKey wallet))
            _      -> Nothing
    in respondToRequest wallet handleEvent

-- | Notify the wallet of all interesting addresses
notifyInterestingAddresses
    :: ( MonadEmulator (TraceError e) m
       , HasWatchAddress s
       )
    => Wallet
    -> ContractTrace s e m a ()
notifyInterestingAddresses wllt =
    void $ interestingAddresses wllt >>= lift . runWallet wllt . traverse_ Wallet.startWatching

-- | Transfer some funds from one wallet to another. This represents a "user
--   action" that runs independently of any contract, just interacting directly
--   with the wallet.
payToWallet
    :: ( MonadEmulator (TraceError e) m )
    => Wallet
    -- ^ The sender
    -> Wallet
    -- ^ The recipient
    -> Value
    -- ^ The amount to be transferred
    -> ContractTrace s e m a ()
payToWallet source target amount =
    let payment = payToPublicKey_ defaultSlotRange amount (EM.walletPubKey target)
     in void $ lift (runWallet source payment)

-- | The wallets used in mockchain simulations by default. There are
--   ten wallets because the emulator comes with ten private keys.
allWallets :: [EM.Wallet]
allWallets = EM.Wallet <$> [1 .. 10]

defaultDist :: InitialDistribution
defaultDist = Map.fromList $ zip allWallets (repeat (Ada.lovelaceValueOf 10000))

makeClassyPrisms ''TraceError

instance EM.AsAssertionError (TraceError e) where
    _AssertionError = _TraceAssertionError
