{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
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
{-# LANGUAGE TypeOperators          #-}
-- | A trace is a sequence of actions by simulated wallets that can be run
--   on the mockchain. This module contains the functions needed to build
--   traces.
module Language.Plutus.Contract.Trace
    ( ContractTrace
    , ContractTraceEffs
    , ContractTraceState
    , TraceError(..)
    , EndpointError(..)
    , AsTraceError(..)
    , toNotifyError
    , WalletState(..)
    , ctsWalletStates
    , ctsContract
    , eventsByWallet
    , handlersByWallet
    , checkpointStoreByWallet
    , ContractTraceResult(..)
    , ctrEmulatorState
    , ctrTraceState
    -- * Running 'ContractTrace' actions
    , runTrace
    , runTraceWithDistribution
    , runTraceWithInitialStates
    , runTraceTxPool
    , evalTrace
    , execTrace
    , setSigningProcess
    -- * Constructing 'ContractTrace' actions
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
    -- * Initial distributions of emulated chains
    , InitialDistribution
    , defaultDist
    , defaultDistFor
    -- * Wallets
    , EM.Wallet(..)
    , EM.walletPubKey
    , EM.walletPrivKey
    , allWallets
    ) where

import           Control.Arrow                                     ((>>>), (>>^))
import           Control.Lens                                      (at, from, makeClassyPrisms, makeLenses, review, use,
                                                                    view, (%=))
import           Control.Monad                                     (guard, replicateM_, unless, void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                         (Error, runError, throwError)
import qualified Control.Monad.Freer.Extras                        as Eff
import           Control.Monad.Freer.Log                           (LogMessage, LogMsg, handleLogWriter, logWarn,
                                                                    mapMLog)
import           Control.Monad.Freer.State                         (State, gets, runState)
import           Control.Monad.Freer.Writer                        (Writer)
import qualified Data.Aeson.Types                                  as JSON
import           Data.Bifunctor                                    (Bifunctor (..))
import           Data.Foldable                                     (toList, traverse_)
import           Data.Map                                          (Map)
import qualified Data.Map                                          as Map
import           Data.Maybe                                        (fromMaybe, mapMaybe)
import           Data.Row                                          (KnownSymbol, Label (..), trial')
import qualified Data.Row                                          as Row
import qualified Data.Row.Extras                                   as V
import qualified Data.Row.Internal                                 as V
import qualified Data.Row.Variants                                 as V
import           Data.Sequence                                     (Seq, (|>))
import           Data.Text.Prettyprint.Doc                         (Pretty, pretty, (<+>))
import           Data.Void                                         (Void)
import           GHC.Generics                                      (Generic)

import           Language.Plutus.Contract                          (Contract (..), HasAwaitSlot, HasTxConfirmation,
                                                                    HasUtxoAt, HasWatchAddress, HasWriteTx, mapError)
import           Language.Plutus.Contract.Checkpoint               (CheckpointStore)
import qualified Language.Plutus.Contract.Resumable                as State
import           Language.Plutus.Contract.Schema                   (Event (..), Handlers (..), Input, Output)
import qualified Language.Plutus.Contract.Types                    as Contract.Types
import qualified Language.Plutus.Contract.Wallet                   as Wallet

import qualified Language.Plutus.Contract.Effects.AwaitSlot        as AwaitSlot
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..))
import qualified Language.Plutus.Contract.Effects.AwaitTxConfirmed as AwaitTxConfirmed
import           Language.Plutus.Contract.Effects.ExposeEndpoint   (HasEndpoint)
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint   as Endpoint
import           Language.Plutus.Contract.Effects.Instance         (HasOwnId)
import qualified Language.Plutus.Contract.Effects.Instance         as OwnInstance
import           Language.Plutus.Contract.Effects.Notify           (HasContractNotify)
import qualified Language.Plutus.Contract.Effects.Notify           as Notify
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
import           Wallet.Emulator                                   (EmulatorState, TxPool, Wallet)
import qualified Wallet.Emulator                                   as EM
import           Wallet.Emulator.MultiAgent                        (EmulatedWalletEffects, _singleton)
import qualified Wallet.Emulator.MultiAgent                        as EM
import           Wallet.Emulator.Notify                            (EmulatorContractNotifyEffect (..),
                                                                    EmulatorNotifyLogMsg (..))
import           Wallet.Emulator.SigningProcess                    (SigningProcess)
import qualified Wallet.Emulator.SigningProcess                    as EM
import           Wallet.Types                                      (ContractInstanceId, EndpointDescription (..),
                                                                    EndpointValue (..), Notification (..),
                                                                    NotificationError (..))

data EndpointError =
    EndpointNotActive (Maybe Wallet) EndpointDescription
    | MoreThanOneEndpointActive EndpointDescription
    deriving stock (Eq, Show, Generic)
    deriving anyclass (JSON.ToJSON, JSON.FromJSON)

instance Pretty EndpointError where
    pretty = \case
        EndpointNotActive w e ->
            "Endpoint not active:" <+> pretty w <+> pretty e
        MoreThanOneEndpointActive e ->
            "More than one endpoint active:" <+> pretty e

toNotifyError :: ContractInstanceId -> EndpointError -> NotificationError
toNotifyError i = \case
    EndpointNotActive _ e       -> EndpointNotAvailable i e
    MoreThanOneEndpointActive e -> MoreThanOneEndpointAvailable i e

-- | Error produced while running a trace. Either a contract-specific
--   error (of type 'e'), or an 'EM.AssertionError' from the emulator.
data TraceError e =
    TraceAssertionError EM.AssertionError
    | TContractError e
    | HandleBlockchainEventsMaxIterationsExceeded Wallet MaxIterations
    | HookError EndpointError
    deriving (Eq, Show)

type InitialDistribution = Map Wallet Value

type ContractTraceEffs s e a =
    '[ EmulatorContractNotifyEffect
     , State (ContractTraceState s (TraceError e) a)
     , Error (TraceError e)
     , State EmulatorState
     ]

type ContractTrace s e a = Eff (ContractTraceEffs s e a)

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
    forall l s e a.
    ( KnownSymbol l )
    => Wallet
    -> Event s
    -> ContractTrace s e a ()
addEvent wallet event = do
    let filterReq Request{rqID, itID, rqRequest=Handlers v} = do
            _ <- trial' v (Label @l)
            Just Response{rspRqID=rqID, rspItID=itID, rspResponse=event}
    hks <- mapMaybe filterReq <$> getHooks @s @e @a wallet >>= \case
            [] -> throwError @(TraceError e)
                $ HookError
                $ EndpointNotActive Nothing
                $ EndpointDescription
                $ show (Label @l)
            [x] -> pure x
            _ -> throwError @(TraceError e)
                $ HookError
                $ MoreThanOneEndpointActive
                $ EndpointDescription
                $ show (Label @l)
    addResponse @s @e @a wallet hks

{-| A variant of 'addEvent' that takes the name of the endpoint as a value
    instead of a type argument. This is useful for the playground where we
    don't have the type-level symbol of user-defined endpoint calls.

    Unfortunately this requires the 'V.Forall (Output s) V.Unconstrained1'
    constraint. Luckily 'V.Forall (Output s) V.Unconstrained1' holds for all
    schemas, so it doesn't restrict the callers of 'addNamedEvent'. But we
    have to propagate it up to the top level :(

-}
addNamedEvent ::
    forall s e a effs.
    ( V.Forall (Output s) V.Unconstrained1 -- TODO: remove
    , Member (Error EndpointError) effs
    , Member (State (ContractTraceState s (TraceError e) a)) effs
    )
    => String -- endpoint name
    -> Wallet
    -> Event s
    -> Eff effs ()
addNamedEvent endpointName wallet event = do
    let filterReq Request{rqID, itID, rqRequest=Handlers v} = do
            guard $
                (V.eraseWithLabels @V.Unconstrained1 (const ()) v)
                    == (endpointName, ())
            Just Response{rspRqID=rqID, rspItID=itID, rspResponse=event}
    hks <- mapMaybe filterReq <$> getHooks @s @e @a wallet >>= \case
            []  -> throwError $ EndpointNotActive Nothing $ EndpointDescription endpointName
            [x] -> pure x
            _   -> throwError $ MoreThanOneEndpointActive $ EndpointDescription endpointName
    addResponse @s @e @a wallet hks


-- | Add a 'Response' to the wallet's trace
addResponse
    :: forall s e a effs.
    ( Member (State (ContractTraceState s (TraceError e) a)) effs
    )
    => Wallet
    -> Response (Event s)
    -> Eff effs ()
addResponse w e = Eff.monadStateToState @(ContractTraceState s (TraceError e) a) $ do
    con <- use ctsContract
    let go st =
            let theState = fromMaybe (emptyWalletState con) st
             in Just (addEventWalletState con e theState)
    ctsWalletStates %= Map.alter go w

-- | Get the hooks that a contract is currently waiting for
getHooks
    :: forall s e a effs.
    ( Member (State (ContractTraceState s (TraceError e) a)) effs )
    => Wallet
    -> Eff effs [Request (Handlers s)]
getHooks w =
    foldMap walletHandlers . Map.lookup w <$> gets @(ContractTraceState s (TraceError e) a) (view ctsWalletStates)

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
    :: forall s e a.
    Wallet
    -> SigningProcess
    -> ContractTrace s e a ()
setSigningProcess wallet signingProcess =
    void $ runWalletControl wallet (EM.setSigningProcess signingProcess)

-- | Run a trace in the emulator and return the
--   final events for each wallet.
execTrace
    :: forall s e a.
    ( V.AllUniqueLabels (Input s)
    , V.Forall (Input s) JSON.FromJSON
    , V.Forall (Output s) V.Unconstrained1
    )
    => Contract s e a
    -> Eff (ContractTraceEffs s e a) ()
    -> Map Wallet [Response (Event s)]
execTrace con action =
    let (e, _) = runTrace con action
    in
        either (const Map.empty) (fmap (toList . walletEvents) . _ctsWalletStates . snd) e

-- | Run a trace in the emulator and return the final state alongside the
--   result
runTrace :: forall s e a.
    ( V.AllUniqueLabels (Input s)
    , V.Forall (Input s) JSON.FromJSON
    , V.Forall (Output s) V.Unconstrained1
    )
    => Contract s e a
    -> Eff (ContractTraceEffs s e a) ()
    -> (Either (TraceError e) ((), ContractTraceState s (TraceError e) a), EmulatorState)
runTrace = runTraceWithDistribution defaultDist

-- | Run a contract and return the result for the given wallet, if it exists
evalTrace ::
    forall s e a.
    ( V.AllUniqueLabels (Input s)
    , V.Forall (Input s) JSON.FromJSON
    , V.Forall (Output s) V.Unconstrained1
    , Show e
    )
    => Contract s e a
    -> Eff (ContractTraceEffs s e a) ()
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

handleEmulatorContractNotify :: forall s e a effs.
    ( V.AllUniqueLabels (Input s)
    , V.Forall (Input s) JSON.FromJSON
    , V.Forall (Output s) V.Unconstrained1
    , Member (State (ContractTraceState s (TraceError e) a)) effs
    , Member (LogMsg EmulatorNotifyLogMsg) effs
    )
    => EmulatorContractNotifyEffect
    ~> Eff effs
handleEmulatorContractNotify = \case
    SendAgentNotification source target notification -> do
        let Notification{notificationContractID,notificationContractEndpoint,notificationContractArg} = notification
            EndpointDescription endpointName = notificationContractEndpoint
            argument = JSON.toJSON $ EndpointValue notificationContractArg

            theEvent :: Either String (V.Var (Input s))
            theEvent = JSON.parseEither (V.namedBranchFromJSON @(Input s) endpointName) (JSON.toJSON argument)

            -- Log the error and return it back to the caller
            returnError :: NotificationError -> Eff effs (Maybe NotificationError)
            returnError e = logWarn (NotifyFailed source e) >> (pure $ Just e)
        case theEvent of
            Left err ->
                let err' = NotificationJSONDecodeError notificationContractEndpoint argument err
                in returnError err'
            Right event -> do
                r <- runError @EndpointError $
                        addNamedEvent @s @e @a endpointName target (Event event)
                either (returnError . toNotifyError notificationContractID) (const $ pure Nothing) r

runTraceWithInitialStates ::
    forall s e a b.
    ( V.AllUniqueLabels (Input s)
    , V.Forall (Input s) JSON.FromJSON
    , V.Forall (Output s) V.Unconstrained1
    )
    => EmulatorState
    -> ContractTraceState s (TraceError e) a
    -> Eff (ContractTraceEffs s e a) b
    -> (Either (TraceError e) (b, ContractTraceState s (TraceError e) a), EmulatorState)
runTraceWithInitialStates initialEmulatorState initialContractState action =
    EM.runEmulator initialEmulatorState
        $ runState initialContractState
        $ interpret (Eff.writeIntoState EM.emulatorLog)
        $ reinterpret @_ @(Writer [LogMessage EM.EmulatorEvent]) (handleLogWriter _singleton)
        $ reinterpret @_ @(LogMsg EM.EmulatorEvent) (mapMLog makeTimed)
        $ reinterpret @_ @(LogMsg EmulatorNotifyLogMsg) (handleEmulatorContractNotify @s @e @a)
        $ action

makeTimed :: Member (State EmulatorState) effs => EmulatorNotifyLogMsg -> Eff effs EM.EmulatorEvent
makeTimed e = do
    emulatorTime <- gets (view (EM.chainState . EM.currentSlot))
    pure $ review (EM.emulatorTimeEvent emulatorTime) (EM.NotificationEvent e)

-- | Run a trace in the emulator and return the final state alongside the
--   result
runTraceWithDistribution ::
    forall s e a b.
    ( V.AllUniqueLabels (Input s)
    , V.Forall (Input s) JSON.FromJSON
    , V.Forall (Output s) V.Unconstrained1
    )
    => InitialDistribution
    -> Contract s e a
    -> Eff (ContractTraceEffs s e a) b
    -> (Either (TraceError e) (b, ContractTraceState s (TraceError e) a), EmulatorState)
runTraceWithDistribution dist con action =
    let -- make sure the wallets know about the initial transaction
        notifyInitial = void (EM.addBlocksAndNotify (Map.keys dist) 1)
        action' = EM.processEmulated @(TraceError e) notifyInitial >> action
        con' = mapError TContractError con
        s = EM.emulatorStateInitialDist (Map.mapKeys EM.walletPubKey dist)
        c = initState (Map.keys dist) con'
    in runTraceWithInitialStates s c action'

-- | Run a 'Trace' on an empty blockchain with a pool of pending transactions.
--   Note: This exists for legacy reasons. 'EM.EmulatorEffs' does not actually
--         let you run any 'Contract's! Only 'ContractTraceEffs' does.
--         Therefore, 'runTraceWithDistribution' and 'runTrace' should be used
--         instead of this.
runTraceTxPool :: forall a.
    TxPool
    -> Eff EM.EmulatorEffs a
    -> (Either (TraceError Void) a, EmulatorState)
runTraceTxPool tp =
    let initialEmulatorState = EM.emulatorStatePool tp
        contract = pure () -- The do-nothing contract
        initialContractState = initState [] contract
    in first (second fst)
        . runTraceWithInitialStates @Row.Empty
            initialEmulatorState
            initialContractState
        . EM.processEmulated @(TraceError Void)

-- | Run a wallet action in the context of the given wallet, notify the wallets,
--   and return the list of new transactions
runWallet :: forall s e a b.
    Wallet
    -> Eff EM.EmulatedWalletEffects b
    -> ContractTrace s e a b
runWallet w = EM.processEmulated @(TraceError e) . EM.walletAction w

runWalletControl :: forall s e a b.
    Wallet
    -> Eff EM.EmulatedWalletControlEffects b
    -> ContractTrace s e a b
runWalletControl w = EM.processEmulated @(TraceError e). EM.walletControlAction w

-- | Call the endpoint on the contract
callEndpoint
    :: forall l ep s e a.
    ( HasEndpoint l ep s )
    => Wallet
    -> ep
    -> ContractTrace s e a ()
callEndpoint wallet ep = do
    -- check if the endpoint is active and throw an error if it isn't
    hks <- getHooks @s @e @a wallet
    unless (any (Endpoint.isActive @l) $ fmap rqRequest hks) $
        throwError @(TraceError e)
            $ HookError
            $ EndpointNotActive (Just wallet)
            $ EndpointDescription
            $ show (Label @l)

    void $ respondToRequest @s @e @a wallet $ RequestHandler $ \req -> do
        guard (Endpoint.isActive @l req)
        pure $ Endpoint.event @l ep

-- | Inspect the open requests of a wallet's contract instance,
--   and maybe respond to them. Returns the response that was provided to the
--   contract, if any.
respondToRequest ::
    forall s e a.
    Wallet
    -- ^ The wallet
    -> RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
    -- ^ How to respond to the requests.
    -> ContractTrace s e a (Maybe (Response (Event s)))
respondToRequest wallet f = do
    hks <- getHooks @s @e @a wallet
    (response :: Maybe (Response (Event s))) <- runWallet @s @e @a wallet $ tryHandler (wrapHandler f) hks
    traverse_ (addResponse @s @e @a wallet) response
    pure response

-- | Get the addresses that are of interest to the wallet's contract instance
interestingAddresses :: forall s e a.
    ( HasWatchAddress s )
    => Wallet
    -> ContractTrace s e a [Address]
interestingAddresses wllt =
    mapMaybe (WatchAddress.watchedAddress . rqRequest) <$> getHooks @s @e @a wllt

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
    :: forall s e a.
    ( HasAwaitSlot s )
    => Wallet
    -> ContractTrace s e a ()
notifySlot wallet = void $ respondToRequest @s @e @a wallet handleSlotNotifications

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
addBlocks' :: forall s e a.
    ( AwaitSlot.HasAwaitSlot s )
    => SlotNotifications -- ^ Whether to notify all wallets after each block.
    -> Integer -- ^ How many blocks to add.
    -> ContractTrace s e a ()
addBlocks' n i = do
    let notify = case n of
            SendSlotNotifications     -> traverse_ (notifySlot @s @e @a) allWallets
            DontSendSlotNotifications -> pure ()

    replicateM_ (fromIntegral i) $ do
        void $ EM.processEmulated @(TraceError e) (EM.addBlocksAndNotify allWallets 1)
        notify

-- | Add a number of empty blocks to the blockchain, updating each wallet's
--   slot after each block
addBlocks :: forall s e a.
    ( AwaitSlot.HasAwaitSlot s )
    => Integer -- ^ How many blocks to add.
    -> ContractTrace s e a ()
addBlocks = addBlocks' @s @e @a SendSlotNotifications

-- | Add blocks until the given slot has been reached.
addBlocksUntil :: forall s e a.
    ( AwaitSlot.HasAwaitSlot s )
    => Slot
    -> ContractTrace s e a ()
addBlocksUntil = addBlocksUntil' @s @e @a SendSlotNotifications

-- | Add blocks until the given slot has been reached.
addBlocksUntil' :: forall s e a.
    ( AwaitSlot.HasAwaitSlot s
    )
    => SlotNotifications
    -> Slot
    -> ContractTrace s e a ()
addBlocksUntil' n sl = do
    currentSlot <- gets (view $ EM.chainState . EM.currentSlot)
    let Slot missing = sl - currentSlot
    addBlocks' @s @e @a n (max 0 missing)

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
handleBlockchainEvents :: forall s e a.
    ( HasUtxoAt s
    , HasWatchAddress s
    , HasWriteTx s
    , HasOwnPubKey s
    , HasTxConfirmation s
    , HasAwaitSlot s
    , HasContractNotify s
    , HasOwnId s
    )
    => Wallet
    -> ContractTrace s e a ()
handleBlockchainEvents =
    handleBlockchainEventsOptions @s @e @a
    defaultHandleBlockchainEventsOptions

-- | Handle all blockchain events for the wallet, throwing an error
--   if the given number of iterations is exceeded
handleBlockchainEventsOptions ::
    forall s e a.
    ( HasUtxoAt s
    , HasWatchAddress s
    , HasWriteTx s
    , HasOwnPubKey s
    , HasTxConfirmation s
    , HasAwaitSlot s
    , HasContractNotify s
    , HasOwnId s
    )
    => HandleBlockchainEventsOptions
    -> Wallet
    -> ContractTrace s e a ()
handleBlockchainEventsOptions o wallet = go 0 where
    HandleBlockchainEventsOptions{maxIterations=MaxIterations i,slotNotifications} = o
    handler = case slotNotifications of
                DontSendSlotNotifications -> handleBlockchainQueries @s
                SendSlotNotifications     ->
                    handleBlockchainQueries <> handleSlotNotifications
    go j | j >= i    = throwError @(TraceError e) (HandleBlockchainEventsMaxIterationsExceeded wallet (MaxIterations i))
         | otherwise = do
             rsp <- respondToRequest @s @e @a wallet handler
             case rsp of
                 Nothing -> pure ()
                 Just _  -> go (j + 1)

handleBlockchainQueries ::
    ( HasWriteTx s
    , HasUtxoAt s
    , HasTxConfirmation s
    , HasOwnPubKey s
    , HasWatchAddress s
    , HasOwnId s
    , HasContractNotify s
    )
    => RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
handleBlockchainQueries =
    handlePendingTransactions
    <> handleUtxoQueries
    <> handleTxConfirmedQueries
    <> handleOwnPubKeyQueries
    <> handleNextTxAtQueries
    <> handleOwnInstanceIdQueries
    <> handleContractNotifications

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

handleOwnInstanceIdQueries ::
    ( HasOwnId s )
    => RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
handleOwnInstanceIdQueries =
    maybeToHandler OwnInstance.request
    >>> RequestHandler.handleOwnInstanceIdQueries
    >>^ OwnInstance.event

handleContractNotifications ::
    ( HasContractNotify s )
    => RequestHandler EmulatedWalletEffects (Handlers s) (Event s)
handleContractNotifications =
    maybeToHandler Notify.request
    >>> RequestHandler.handleContractNotifications
    >>^ Notify.event

-- | Notify the wallet of all interesting addresses
notifyInterestingAddresses :: forall s e a.
    ( HasWatchAddress s )
    => Wallet
    -> ContractTrace s e a ()
notifyInterestingAddresses wllt =
    void $ interestingAddresses @s @e @a wllt >>= runWallet @s @e @a wllt . traverse_ Wallet.startWatching

-- | Transfer some funds from one wallet to another. This represents a "user
--   action" that runs independently of any contract, just interacting directly
--   with the wallet.
payToWallet :: forall s e a.
    Wallet
    -- ^ The sender
    -> Wallet
    -- ^ The recipient
    -> Value
    -- ^ The amount to be transferred
    -> ContractTrace s e a ()
payToWallet source target amount =
    let payment = payToPublicKey_ defaultSlotRange amount (EM.walletPubKey target)
     in void $ runWallet source payment

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
