{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
module Language.Plutus.Contract.Trace.RequestHandler(
    RequestHandler(..)
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
    ) where

import           Control.Applicative                (Alternative (empty))
import           Control.Arrow                      (Arrow, Kleisli (..))
import Control.Category (Category)
import Data.Foldable (traverse_)
import qualified Ledger.AddressMap as AM
import           Control.Lens
import           Control.Monad                      (foldM, guard)
import           Control.Monad.Freer
import qualified Control.Monad.Freer.Error                         as Eff
import           Control.Monad.Freer.NonDet         (NonDet)
import qualified Control.Monad.Freer.NonDet         as NonDet
import qualified Data.Map as Map
import           Data.Monoid                        (Alt (..), Ap (..))
import qualified Data.Text as Text

import           Language.Plutus.Contract.Resumable (Request (..), Response (..))

import Ledger (PubKey, Slot, Tx, Address, TxId)
import           Ledger.AddressMap                          (AddressMap(..))
import           Ledger.Constraints.OffChain (UnbalancedTx(unBalancedTxTx))
import Control.Monad.Freer.Log (Log, surroundDebug, logWarn, logDebug)
import qualified Wallet.Effects
import Language.Plutus.Contract.Effects.UtxoAt (UtxoAtAddress(..))
import Language.Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed(..))
import Wallet.Effects (WalletEffect, SigningProcessEffect, ChainIndexEffect, AddressChangeRequest(..), AddressChangeResponse)
import           Wallet.API                                        (WalletAPIError)
import qualified Language.Plutus.Contract.Wallet                   as Wallet


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
    , Member Log effs
    )
    => RequestHandler effs a PubKey
handleOwnPubKey = 
    RequestHandler $ \_ ->
        surroundDebug "handleOwnPubKey" Wallet.Effects.ownPubKey

handleSlotNotifications ::
    forall effs.
    ( Member WalletEffect effs
    , Member Log effs
    )
    => RequestHandler effs Slot Slot
handleSlotNotifications =
    RequestHandler $ \targetSlot -> 
        surroundDebug "handleSlotNotifications" $ do
            currentSlot <- Wallet.Effects.walletSlot
            logDebug $ Text.pack $ "targetSlot: " <> show targetSlot <> "; current slot: " <> show currentSlot
            guard (currentSlot >= targetSlot)
            pure currentSlot

handlePendingTransactions ::
    forall effs.
    ( Member WalletEffect effs
    , Member Log effs
    , Member SigningProcessEffect effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs UnbalancedTx (Either WalletAPIError Tx)
handlePendingTransactions =
    RequestHandler $ \unbalancedTx ->
        surroundDebug "handlePendingTransactions" $ do
        logDebug "Start watching contract addresses."
        wa <- Wallet.Effects.watchedAddresses
        traverse_ Wallet.Effects.startWatching (AM.addressesTouched wa (unBalancedTxTx unbalancedTx))
        (Right <$> Wallet.handleTx unbalancedTx) `Eff.handleError` (\err -> logWarn "handleTxFailed" >> pure (Left err))

handleUtxoQueries ::
    forall effs.
    ( Member Log effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs Address UtxoAtAddress
handleUtxoQueries = RequestHandler $ \addr ->
    surroundDebug "handleUtxoQueries" $ do
        Wallet.Effects.startWatching addr
        AddressMap utxoSet <- Wallet.Effects.watchedAddresses
        maybe empty (pure . UtxoAtAddress addr) $ Map.lookup addr utxoSet

handleTxConfirmedQueries ::
    forall effs.
    ( Member Log effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs TxId TxConfirmed
handleTxConfirmedQueries = RequestHandler $ \txid ->
    surroundDebug "handleTxConfirmedQueries" $ do
        conf <- Wallet.Effects.transactionConfirmed txid
        guard conf
        pure (TxConfirmed txid)

handleNextTxAtQueries ::
    forall effs.
    ( Member Log effs
    , Member WalletEffect effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs AddressChangeRequest AddressChangeResponse
handleNextTxAtQueries = RequestHandler $ \req ->
    surroundDebug "handleNextTxAtQueries" $ do
        sl <- Wallet.Effects.walletSlot
        guard (sl >= acreqSlot req)
        Wallet.Effects.nextTx req