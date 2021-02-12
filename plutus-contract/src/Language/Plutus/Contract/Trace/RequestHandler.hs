{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
module Language.Plutus.Contract.Trace.RequestHandler(
    RequestHandler(..)
    , RequestHandlerLogMsg(..)
    , tryHandler
    , wrapHandler
    , extract
    , maybeToHandler
    -- * handlers for common requests
    , handleOwnPubKey
    , handleSlotNotifications
    , handlePendingTransactions
    , handleUtxoQueries
    , handleTxConfirmedQueries
    , handleNextTxAtQueries
    , handleOwnInstanceIdQueries
    , handleContractNotifications
    ) where

import           Control.Applicative                               (Alternative (empty))
import           Control.Arrow                                     (Arrow, Kleisli (..))
import           Control.Category                                  (Category)
import           Control.Lens
import           Control.Monad                                     (foldM, guard)
import           Control.Monad.Freer
import qualified Control.Monad.Freer.Error                         as Eff
import           Control.Monad.Freer.NonDet                        (NonDet)
import qualified Control.Monad.Freer.NonDet                        as NonDet
import           Control.Monad.Freer.Reader                        (Reader, ask)
import           Data.Foldable                                     (traverse_)
import qualified Data.Map                                          as Map
import           Data.Monoid                                       (Alt (..), Ap (..))
import           Data.Text                                         (Text)
import qualified Ledger.AddressMap                                 as AM

import           Language.Plutus.Contract.Resumable                (Request (..), Response (..))

import           Control.Monad.Freer.Extras.Log                    (LogMessage, LogMsg, LogObserve, logDebug, logWarn,
                                                                    surroundDebug)
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..))
import           Language.Plutus.Contract.Effects.Instance         (OwnIdRequest)
import           Language.Plutus.Contract.Effects.UtxoAt           (UtxoAtAddress (..))
import qualified Language.Plutus.Contract.Wallet                   as Wallet
import           Ledger                                            (Address, PubKey, Slot, Tx, TxId)
import           Ledger.AddressMap                                 (AddressMap (..))
import           Ledger.Constraints.OffChain                       (UnbalancedTx (unBalancedTxTx))
import           Wallet.API                                        (WalletAPIError)
import           Wallet.Effects                                    (ChainIndexEffect, ContractRuntimeEffect,
                                                                    WalletEffect)
import qualified Wallet.Effects
import           Wallet.Emulator.LogMessages                       (RequestHandlerLogMsg (..), TxBalanceMsg)
import           Wallet.Types                                      (AddressChangeRequest (..), AddressChangeResponse,
                                                                    ContractInstanceId, Notification, NotificationError)


-- | Request handlers that can choose whether to handle an effect (using
--   'Alternative'). This is useful if 'req' is a sum type.
newtype RequestHandler effs req resp = RequestHandler { unRequestHandler :: req -> Eff (NonDet ': effs) resp }
    deriving stock (Functor)
    deriving (Profunctor, Category, Arrow) via (Kleisli (Eff (NonDet ': effs)))
    deriving (Semigroup, Monoid) via (Ap ((->) req) (Alt (Eff (NonDet ': effs)) resp))

-- Try the handler on the requests until it succeeds for the first time, then stop.
tryHandler ::
    forall effs req resp
    . RequestHandler effs req resp
    -> [req]
    -> Eff effs (Maybe resp)
tryHandler (RequestHandler h) requests =
    foldM (\e i -> maybe (NonDet.makeChoiceA @Maybe $ h i) (pure . Just) e) Nothing requests

extract :: Alternative f => Prism' a b -> a -> f b
extract p = maybe empty pure . preview p

wrapHandler :: RequestHandler effs req resp -> RequestHandler effs (Request req) (Response resp)
wrapHandler (RequestHandler h) = RequestHandler $ \Request{rqID, itID, rqRequest} -> do
    r <- h rqRequest
    pure $ Response{rspRqID = rqID, rspResponse = r, rspItID = itID }

maybeToHandler :: (req -> Maybe resp) -> RequestHandler effs req resp
maybeToHandler f = RequestHandler $ maybe empty pure . f

-- handlers for common requests

handleOwnPubKey ::
    forall a effs.
    ( Member WalletEffect effs
    , Member (LogObserve (LogMessage Text)) effs
    )
    => RequestHandler effs a PubKey
handleOwnPubKey =
    RequestHandler $ \_ ->
        surroundDebug @Text "handleOwnPubKey" Wallet.Effects.ownPubKey

handleSlotNotifications ::
    forall effs.
    ( Member WalletEffect effs
    , Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    )
    => RequestHandler effs Slot Slot
handleSlotNotifications =
    RequestHandler $ \targetSlot ->
        surroundDebug @Text "handleSlotNotifications" $ do
            currentSlot <- Wallet.Effects.walletSlot
            logDebug $ SlotNoficationTargetVsCurrent targetSlot currentSlot
            guard (currentSlot >= targetSlot)
            pure currentSlot

handlePendingTransactions ::
    forall effs.
    ( Member WalletEffect effs
    , Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member (LogMsg TxBalanceMsg) effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs UnbalancedTx (Either WalletAPIError Tx)
handlePendingTransactions =
    RequestHandler $ \unbalancedTx ->
        surroundDebug @Text "handlePendingTransactions" $ do
        logDebug StartWatchingContractAddresses
        wa <- Wallet.Effects.watchedAddresses
        traverse_ Wallet.Effects.startWatching (AM.addressesTouched wa (unBalancedTxTx unbalancedTx))
        (Right <$> Wallet.handleTx unbalancedTx) `Eff.handleError` (\err -> logWarn (HandleTxFailed err) >> pure (Left err))

handleUtxoQueries ::
    forall effs.
    ( Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs Address UtxoAtAddress
handleUtxoQueries = RequestHandler $ \addr ->
    surroundDebug @Text "handleUtxoQueries" $ do
        Wallet.Effects.startWatching addr
        AddressMap utxoSet <- Wallet.Effects.watchedAddresses
        case Map.lookup addr utxoSet of
            Nothing -> do
                logWarn $ UtxoAtFailed addr
                empty
            Just s  -> pure (UtxoAtAddress addr s)

handleTxConfirmedQueries ::
    forall effs.
    ( Member (LogObserve (LogMessage Text)) effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs TxId TxConfirmed
handleTxConfirmedQueries = RequestHandler $ \txid ->
    surroundDebug @Text "handleTxConfirmedQueries" $ do
        conf <- Wallet.Effects.transactionConfirmed txid
        guard conf
        pure (TxConfirmed txid)

handleNextTxAtQueries ::
    forall effs.
    ( Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member WalletEffect effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs AddressChangeRequest AddressChangeResponse
handleNextTxAtQueries = RequestHandler $ \req ->
    surroundDebug @Text "handleNextTxAtQueries" $ do
        current <- Wallet.Effects.walletSlot
        let target = acreqSlot req
        logDebug $ HandleNextTxAt current target
        -- If we ask the chain index for transactions that were confirmed in
        -- the current slot, we always get an empty list, because the chain
        -- index only learns about those transactions at the beginning of the
        -- next slot. So we need to make sure that we are past the current
        -- slot.
        guard (current > target)
        Wallet.Effects.nextTx req

handleOwnInstanceIdQueries ::
    forall effs.
    ( Member (LogObserve (LogMessage Text)) effs
    , Member (Reader ContractInstanceId) effs
    )
    => RequestHandler effs OwnIdRequest ContractInstanceId
handleOwnInstanceIdQueries = RequestHandler $ \_ ->
    surroundDebug @Text "handleOwnInstanceIdQueries" ask

handleContractNotifications ::
    forall effs.
    ( Member (LogObserve (LogMessage Text)) effs
    , Member ContractRuntimeEffect effs
    )
    => RequestHandler effs Notification (Maybe NotificationError)
handleContractNotifications = RequestHandler $
    surroundDebug @Text "handleContractNotifications" . Wallet.Effects.sendNotification
