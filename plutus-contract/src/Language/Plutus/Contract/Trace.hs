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
{-# LANGUAGE TypeFamilies           #-}
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
    , SlotNotifications(..)
    , runWallet
    , getHooks
    , callEndpoint
    , handleUtxoQueries
    , handleNextTxAtQueries
    , addBlocks
    , addBlocks'
    , addBlocksUntil
    , addBlocksUntil'
    , addEvent
    , addNamedEvent
    , addResponse
    , notifyInterestingAddresses
    , notifySlot
    , payToWallet
    , respondToRequest
    -- * Handle blockchain events repeatedly
    , MaxIterations(..)
    , defaultMaxIterations
    , HandleBlockchainEventsOptions(..)
    , defaultHandleBlockchainEventsOptions
    , handleBlockchainEvents
    , handleBlockchainEventsOptions
    -- * Running 'MonadEmulator' actions
    , MonadEmulator
    , InitialDistribution
    , withInitialDistribution
    , defaultDist
    , defaultDistFor
    -- * Wallets
    , EM.Wallet(..)
    , EM.walletPubKey
    , EM.walletPrivKey
    , allWallets
    ) where

import           Control.Arrow                                     ((>>>), (>>^))
import           Control.Lens                                      (at, from, makeClassyPrisms, makeLenses, use, view,
                                                                    (%=))
import           Control.Monad.Except
import qualified Control.Monad.Freer                               as Eff
import           Control.Monad.Reader                              ()
import           Control.Monad.State                               (MonadState, StateT, runStateT)
import           Data.Bifunctor                                    (Bifunctor (..))
import           Data.Foldable                                     (toList, traverse_)
import           Data.Map                                          (Map)
import qualified Data.Map                                          as Map
import           Data.Maybe                                        (fromMaybe, mapMaybe)
import           Data.Row                                          (KnownSymbol, Label (..), trial')
import qualified Data.Row.Internal                                 as V
import qualified Data.Row.Variants                                 as V
import           Data.Sequence                                     (Seq, (|>))
import           Data.Text                                         (Text)
import qualified Data.Text                                         as Text
import           Data.Text.Extras                                  (tshow)

import           Language.Plutus.Contract                          (Contract (..), HasAwaitSlot, HasTxConfirmation,
                                                                    HasUtxoAt, HasWatchAddress, HasWriteTx, mapError)
import           Language.Plutus.Contract.Checkpoint               (CheckpointStore)
import qualified Language.Plutus.Contract.Resumable                as State
import           Language.Plutus.Contract.Schema                   (Event (..), Handlers (..), Output)
import qualified Language.Plutus.Contract.Types                    as Contract.Types
import qualified Language.Plutus.Contract.Wallet                   as Wallet

import qualified Language.Plutus.Contract.Effects.AwaitSlot        as AwaitSlot
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..))
import qualified Language.Plutus.Contract.Effects.AwaitTxConfirmed as AwaitTxConfirmed
import           Language.Plutus.Contract.Effects.ExposeEndpoint   (HasEndpoint)
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint   as Endpoint
import           Language.Plutus.Contract.Effects.OwnPubKey        (HasOwnPubKey)
import qualified Language.Plutus.Contract.Effects.OwnPubKey        as OwnPubKey
import qualified Language.Plutus.Contract.Effects.UtxoAt           as UtxoAt
import qualified Language.Plutus.Contract.Effects.WatchAddress     as WatchAddress
import qualified Language.Plutus.Contract.Effects.WriteTx          as WriteTx
import           Language.Plutus.Contract.Resumable                (Request (..), Requests (..), Response (..))
import           Language.Plutus.Contract.Trace.RequestHandler     (MaxIterations (..), RequestHandler (..),
                                                                    defaultMaxIterations, maybeToHandler, tryHandler,
                                                                    wrapHandler)
import qualified Language.Plutus.Contract.Trace.RequestHandler     as RequestHandler
import           Language.Plutus.Contract.Types                    (ResumableResult (..))

import qualified Ledger.Ada                                        as Ada
import           Ledger.Address                                    (Address)
import           Ledger.Slot                                       (Slot (..))
import           Ledger.Value                                      (Value)

import           Wallet.API                                        (defaultSlotRange, payToPublicKey_)
import           Wallet.Emulator                                   (EmulatorAction, EmulatorState, MonadEmulator,
                                                                    Wallet)
import qualified Wallet.Emulator                                   as EM
import           Wallet.Emulator.MultiAgent                        (EmulatedWalletEffects)
import qualified Wallet.Emulator.MultiAgent                        as EM
import           Wallet.Emulator.SigningProcess                    (SigningProcess)
import qualified Wallet.Emulator.SigningProcess                    as EM

-- | Error produced while running a trace. Either a contract-specific
--   error (of type 'e'), or an 'EM.AssertionError' from the emulator.
data TraceError e =
    TraceAssertionError EM.AssertionError
    | TContractError e
    | HandleBlockchainEventsMaxIterationsExceeded Wallet MaxIterations
    | HookError Text
    deriving (Eq, Show)

type InitialDistribution = Map Wallet Value

type ContractTrace s e m a = StateT (ContractTraceState s (TraceError e) a) m

data WalletState s e a =
    WalletState
        { walletContractState   :: ResumableResult e (Event s) (Handlers s) a
        , walletEvents          :: Seq (Response (Event s))
        , walletHandlersHistory :: Seq [State.Request (Handlers s)]
        }

walletHandlers :: WalletState s (TraceError e) a -> [State.Request (Handlers s)]
walletHandlers = State.unRequests . wcsRequests . walletContractState

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
    let ResumableResult{wcsResponses,wcsRequests=Requests{unRequests},wcsCheckpointStore} = walletContractState
        state' = Contract.Types.insertAndUpdate c wcsCheckpointStore wcsResponses event
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
checkpointStoreByWallet = fmap (wcsCheckpointStore . walletContractState) . _ctsWalletStates

makeLenses ''ContractTraceState

initState ::
    [Wallet]
    -> Contract s e a
    -> ContractTraceState s e a
initState wllts con = ContractTraceState wallets con where
    wallets = Map.fromList $ fmap (\a -> (a,emptyWalletState con)) wllts

{-| Add an event to the wallet's trace. This verifies that the contract
    currently has exactly one open request for the symbol @l@, and throws
    a @HookError@ if it has 0, or more than 1, requests. Consider using
    'respondToRequest' if you want to explicitly choose which request to
    respond to.
-}
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

{-| A variant of 'addEvent' that takes the name of the endpoint as a value
    instead of a type argument. This is useful for the playground where we
    don't have the type-level symbol of user-defined endpoint calls.

    Unfortunately this requires the 'V.Forall (Output s) V.Unconstrained1'
    constraint. Luckily 'V.Forall (Output s) V.Unconstrained1' holds for all
    schemas, so it doesn't restrict the callers of 'addNamedEvent'. But we
    have to propagate it up to the top level :(

-}
addNamedEvent ::
    forall s e m a.
    ( MonadEmulator (TraceError e) m
    , V.Forall (Output s) V.Unconstrained1 -- TODO: remove
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
    Show e
    => Contract s e a
    -> ContractTrace s e (EmulatorAction (TraceError e)) a ()
    -> Wallet
    -> Either String a
evalTrace contract trace wllt = do
    (_, state) <- first (const "contract trace failed") $ fst $ runTrace @s @e contract trace
    wlltState <- maybe (Left "wallet state not found") pure $ view (ctsWalletStates . at wllt) state
    let ResumableResult{wcsFinalState} = walletContractState wlltState
    case wcsFinalState of
        Right (Just a) -> pure a
        Right Nothing  -> Left "contract not finished"
        Left err       -> Left $ "contract failed for wallet " <> show wllt <> " with " <> show err

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
    -> m a
runWallet w = EM.processEmulated . EM.walletAction w

runWalletControl
    :: ( MonadEmulator (TraceError e) m )
    => Wallet
    -> Eff.Eff EM.EmulatedWalletControlEffects a
    -> m a
runWalletControl w = EM.processEmulated . EM.walletControlAction w

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

    void $ respondToRequest wallet $ RequestHandler $ \req -> do
        guard (Endpoint.isActive @l req)
        pure $ Endpoint.event @l ep

-- | Inspect the open requests of a wallet's contract instance,
--   and maybe respond to them. Returns the response that was provided to the
--   contract, if any.
respondToRequest ::
    forall s e m a.
    ( MonadEmulator (TraceError e) m
    )
    => Wallet
    -- ^ The wallet
    -> RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
    -- ^ How to respond to the requests.
    -> ContractTrace s e m a (Maybe (Response (Event s)))
respondToRequest wallet f = do
    hks <- getHooks wallet
    (response :: Maybe (Response (Event s))) <- lift $ runWallet wallet $ tryHandler (wrapHandler f) hks
    traverse_ (addResponse wallet) response
    pure response

-- | Get the addresses that are of interest to the wallet's contract instance
interestingAddresses
    :: ( MonadEmulator (TraceError e) m
       , HasWatchAddress s
       )
    => Wallet
    -> ContractTrace s e m a [Address]
interestingAddresses wllt =
    mapMaybe (WatchAddress.watchedAddress . rqRequest) <$> getHooks wllt

handleSlotNotifications ::
    ( HasAwaitSlot s
    )
    => RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
handleSlotNotifications =
    maybeToHandler AwaitSlot.request
    >>> RequestHandler.handleSlotNotifications
    >>^ AwaitSlot.event

-- | Check whether the wallet's contract instance is waiting to be notified
--   of a slot, and send the notification.
notifySlot
    :: forall s e m a.
       ( MonadEmulator (TraceError e) m
       , HasAwaitSlot s
       )
    => Wallet
    -> ContractTrace s e m a ()
notifySlot wallet = void $ respondToRequest wallet handleSlotNotifications

-- | Whether to update the internal slot counter of a wallet (that is, the wallet's notion
--   of the current time)
data SlotNotifications =
        SendSlotNotifications
        | DontSendSlotNotifications
    deriving (Eq, Ord, Show)

-- | @defaultSlotNotifications = SendSlotNotifications@
defaultSlotNotifications :: SlotNotifications
defaultSlotNotifications = SendSlotNotifications

-- | Add a number of empty blocks to the blockchain.
addBlocks'
    :: ( MonadEmulator (TraceError e) m
       , AwaitSlot.HasAwaitSlot s
       )
    => SlotNotifications -- ^ Whether to notify all wallets after each block.
    -> Integer -- ^ How many blocks to add.
    -> ContractTrace s e m a ()
addBlocks' n i = do
    let notify = case n of
            SendSlotNotifications     -> traverse_ notifySlot allWallets
            DontSendSlotNotifications -> pure ()

    replicateM_ (fromIntegral i) $ do
        void $ lift $ EM.processEmulated (EM.addBlocksAndNotify allWallets 1)
        notify

-- | Add a number of empty blocks to the blockchain, updating each wallet's
--   slot after each block
addBlocks
    :: ( MonadEmulator (TraceError e) m
       , AwaitSlot.HasAwaitSlot s
       )
    => Integer -- ^ How many blocks to add.
    -> ContractTrace s e m a ()
addBlocks = addBlocks' SendSlotNotifications

-- | Add blocks until the given slot has been reached.
addBlocksUntil
    :: ( MonadEmulator (TraceError e) m
       , AwaitSlot.HasAwaitSlot s
       )
    => Slot
    -> ContractTrace s e m a ()
addBlocksUntil = addBlocksUntil' SendSlotNotifications

-- | Add blocks until the given slot has been reached.
addBlocksUntil'
    :: ( MonadEmulator (TraceError e) m
       , AwaitSlot.HasAwaitSlot s
       )
    => SlotNotifications
    -> Slot
    -> ContractTrace s e m a ()
addBlocksUntil' n sl = do
    currentSlot <- lift $ use (EM.chainState . EM.currentSlot)
    let Slot missing = sl - currentSlot
    addBlocks' n (max 0 missing)

-- | Options for 'handleBlockchainEvents'
data HandleBlockchainEventsOptions =
    HandleBlockchainEventsOptions
        { maxIterations     :: MaxIterations
        , slotNotifications :: SlotNotifications
        }

defaultHandleBlockchainEventsOptions :: HandleBlockchainEventsOptions
defaultHandleBlockchainEventsOptions =
    HandleBlockchainEventsOptions
        { maxIterations = defaultMaxIterations
        , slotNotifications = defaultSlotNotifications
        }

-- | Handle all blockchain events for the wallet, throwing an error
--   if there are unhandled events after 'defaultMaxIterations'.
handleBlockchainEvents
    :: ( MonadEmulator (TraceError e) m
       , HasUtxoAt s
       , HasWatchAddress s
       , HasWriteTx s
       , HasOwnPubKey s
       , HasTxConfirmation s
       , HasAwaitSlot s
       )
    => Wallet
    -> ContractTrace s e m a ()
handleBlockchainEvents = handleBlockchainEventsOptions defaultHandleBlockchainEventsOptions

-- | Handle all blockchain events for the wallet, throwing an error
--   if the given number of iterations is exceeded
handleBlockchainEventsOptions ::
    forall s e m a.
    ( MonadEmulator (TraceError e) m
    , HasUtxoAt s
    , HasWatchAddress s
    , HasWriteTx s
    , HasOwnPubKey s
    , HasTxConfirmation s
    , HasAwaitSlot s
    )
    => HandleBlockchainEventsOptions
    -> Wallet
    -> ContractTrace s e m a ()
handleBlockchainEventsOptions o wallet = go 0 where
    HandleBlockchainEventsOptions{maxIterations=MaxIterations i,slotNotifications} = o
    handler = case slotNotifications of
                DontSendSlotNotifications -> handleBlockchainQueries @s
                SendSlotNotifications     ->
                    handleBlockchainQueries <> handleSlotNotifications
    go j | j >= i    = lift (throwError (HandleBlockchainEventsMaxIterationsExceeded wallet (MaxIterations i)))
         | otherwise = do
             rsp <- respondToRequest wallet handler
             case rsp of
                 Nothing -> pure ()
                 Just _  -> go (j + 1)

handleBlockchainQueries ::
    ( HasWriteTx s
    , HasUtxoAt s
    , HasTxConfirmation s
    , HasOwnPubKey s
    , HasWatchAddress s
    )
    => RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
handleBlockchainQueries =
    handlePendingTransactions
    <> handleUtxoQueries
    <> handleTxConfirmedQueries
    <> handleOwnPubKeyQueries
    <> handleNextTxAtQueries

-- | Submit the wallet's pending transactions to the blockchain
--   and inform all wallets about new transactions and respond to
--   UTXO queries
handlePendingTransactions ::
    ( HasWriteTx s
    )
    => RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
handlePendingTransactions =
    maybeToHandler WriteTx.pendingTransaction
    >>> RequestHandler.handlePendingTransactions
    >>^ WriteTx.event . view (from WriteTx.writeTxResponse)

-- | Look at the "utxo-at" requests of the contract and respond to all of them
--   with the current UTXO set at the given address.
handleUtxoQueries ::
    ( HasUtxoAt s
    )
    => RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
handleUtxoQueries =
    maybeToHandler UtxoAt.utxoAtRequest
    >>> RequestHandler.handleUtxoQueries
    >>^ UtxoAt.event

handleTxConfirmedQueries ::
    ( HasTxConfirmation s
    )
    => RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
handleTxConfirmedQueries =
    maybeToHandler AwaitTxConfirmed.txId
    >>> RequestHandler.handleTxConfirmedQueries
    >>^ AwaitTxConfirmed.event . unTxConfirmed

handleNextTxAtQueries
    :: ( HasWatchAddress s
       )
    => RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
handleNextTxAtQueries =
    maybeToHandler WatchAddress.watchAddressRequest
    >>> RequestHandler.handleNextTxAtQueries
    >>^ WatchAddress.event

handleOwnPubKeyQueries ::
    ( HasOwnPubKey s
    )
    => RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
handleOwnPubKeyQueries =
    maybeToHandler OwnPubKey.request
    >>> RequestHandler.handleOwnPubKey
    >>^ OwnPubKey.event

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
defaultDist = defaultDistFor allWallets

defaultDistFor :: [EM.Wallet] -> InitialDistribution
defaultDistFor wallets = Map.fromList $ zip wallets (repeat (Ada.lovelaceValueOf 10000))

makeClassyPrisms ''TraceError

instance EM.AsAssertionError (TraceError e) where
    _AssertionError = _TraceAssertionError
