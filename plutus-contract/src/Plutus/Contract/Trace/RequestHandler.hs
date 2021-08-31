{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
module Plutus.Contract.Trace.RequestHandler(
    RequestHandler(..)
    , RequestHandlerLogMsg(..)
    , tryHandler
    , tryHandler'
    , wrapHandler
    , extract
    , maybeToHandler
    , generalise
    -- * handlers for common requests
    , handleOwnPubKey
    , handleSlotNotifications
    , handleCurrentSlot
    , handleTimeNotifications
    , handleCurrentTime
    , handleTimeToSlotConversions
    , handleUnbalancedTransactions
    , handlePendingTransactions
    , handleChainIndexQueries
    , handleOwnInstanceIdQueries
    ) where

import           Control.Applicative            (Alternative (empty, (<|>)))
import           Control.Arrow                  (Arrow, Kleisli (..))
import           Control.Category               (Category)
import           Control.Lens
import           Control.Monad                  (foldM, guard, join)
import           Control.Monad.Freer
import qualified Control.Monad.Freer.Error      as Eff
import           Control.Monad.Freer.NonDet     (NonDet)
import qualified Control.Monad.Freer.NonDet     as NonDet
import           Control.Monad.Freer.Reader     (Reader, ask)
import           Data.Monoid                    (Alt (..), Ap (..))
import           Data.Text                      (Text)

import           Plutus.Contract.Resumable      (Request (..), Response (..))

import           Control.Monad.Freer.Extras.Log (LogMessage, LogMsg, LogObserve, logDebug, logWarn, surroundDebug)
import           Ledger                         (POSIXTime, POSIXTimeRange, PubKey, Slot, SlotRange, Tx)
import           Ledger.Constraints.OffChain    (UnbalancedTx)
import qualified Ledger.TimeSlot                as TimeSlot
import           Plutus.ChainIndex              (ChainIndexQueryEffect)
import qualified Plutus.ChainIndex.Effects      as ChainIndexEff
import           Plutus.Contract.Effects        (ChainIndexQuery (..), ChainIndexResponse (..))
import qualified Plutus.Contract.Wallet         as Wallet
import           Wallet.API                     (WalletAPIError)
import           Wallet.Effects                 (NodeClientEffect, WalletEffect)
import qualified Wallet.Effects
import           Wallet.Emulator.LogMessages    (RequestHandlerLogMsg (..))
import           Wallet.Types                   (ContractInstanceId)


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
tryHandler handler = tryHandler' (Just <$> handler)

-- Try the handler on the requests, using the 'Alternative' instance of @f@
tryHandler' ::
    forall f effs req resp
    . (Alternative f, Monad f)
    => RequestHandler effs req (f resp)
    -> [req]
    -> Eff effs (f resp)
tryHandler' (RequestHandler h) requests =
    foldM (\e i -> fmap (e <|>) $ fmap join $ NonDet.makeChoiceA @f $ h i) empty requests

extract :: Alternative f => Prism' a b -> a -> f b
extract p = maybe empty pure . preview p

-- | Generalise a request handler
generalise ::
    forall effs req req' resp resp'
    . (req' -> Maybe req)
    -> (resp -> resp')
    -> RequestHandler effs req resp
    -> RequestHandler effs req' resp'
generalise rq rsp (RequestHandler h) = RequestHandler $ \k -> do
    case rq k of
        Nothing -> empty
        Just k' -> rsp <$> h k'

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
    ( Member NodeClientEffect effs
    , Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    )
    => RequestHandler effs Slot Slot
handleSlotNotifications =
    RequestHandler $ \targetSlot_ ->
        surroundDebug @Text "handleSlotNotifications" $ do
            currentSlot <- Wallet.Effects.getClientSlot
            logDebug $ SlotNoticationTargetVsCurrent targetSlot_ currentSlot
            guard (currentSlot >= targetSlot_)
            pure currentSlot

handleTimeNotifications ::
    forall effs.
    ( Member NodeClientEffect effs
    , Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    )
    => RequestHandler effs POSIXTime POSIXTime
handleTimeNotifications =
    RequestHandler $ \targetTime_ ->
        surroundDebug @Text "handleTimeNotifications" $ do
            currentSlot <- Wallet.Effects.getClientSlot
            slotConfig <- Wallet.Effects.getClientSlotConfig
            let targetSlot_ = TimeSlot.posixTimeToEnclosingSlot slotConfig targetTime_
            logDebug $ SlotNoticationTargetVsCurrent targetSlot_ currentSlot
            guard (currentSlot >= targetSlot_)
            pure $ TimeSlot.slotToEndPOSIXTime slotConfig currentSlot

handleCurrentSlot ::
    forall effs a.
    ( Member NodeClientEffect effs
    , Member (LogObserve (LogMessage Text)) effs
    )
    => RequestHandler effs a Slot
handleCurrentSlot =
    RequestHandler $ \_ ->
        surroundDebug @Text "handleCurrentSlot" $ do
            Wallet.Effects.getClientSlot

handleCurrentTime ::
    forall effs a.
    ( Member NodeClientEffect effs
    , Member (LogObserve (LogMessage Text)) effs
    )
    => RequestHandler effs a POSIXTime
handleCurrentTime =
    RequestHandler $ \_ ->
        surroundDebug @Text "handleCurrentTime" $ do
            slotConfig <- Wallet.Effects.getClientSlotConfig
            TimeSlot.slotToEndPOSIXTime slotConfig <$> Wallet.Effects.getClientSlot

handleTimeToSlotConversions ::
    forall effs.
    ( Member NodeClientEffect effs
    , Member (LogObserve (LogMessage Text)) effs
    )
    => RequestHandler effs POSIXTimeRange SlotRange
handleTimeToSlotConversions =
    RequestHandler $ \poxisTimeRange ->
        surroundDebug @Text "handleTimeToSlotConversions" $ do
            slotConfig <- Wallet.Effects.getClientSlotConfig
            pure $ TimeSlot.posixTimeRangeToContainedSlotRange slotConfig poxisTimeRange

handleUnbalancedTransactions ::
    forall effs.
    ( Member WalletEffect effs
    , Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    )
    => RequestHandler effs UnbalancedTx (Either WalletAPIError Tx)
handleUnbalancedTransactions =
    RequestHandler $ \unbalancedTx ->
        surroundDebug @Text "handleUnbalancedTransactions" $ do
        Wallet.balanceTx unbalancedTx `Eff.handleError` (\err -> logWarn (HandleTxFailed err) >> pure (Left err))

handlePendingTransactions ::
    forall effs.
    ( Member WalletEffect effs
    , Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    )
    => RequestHandler effs Tx (Either WalletAPIError Tx)
handlePendingTransactions =
    RequestHandler $ \tx ->
        surroundDebug @Text "handlePendingTransactions" $ do
        Eff.handleError (Right <$> Wallet.signTxAndSubmit tx)
                        (\err -> logWarn (HandleTxFailed err) >> pure (Left err))

handleChainIndexQueries ::
    forall effs.
    ( Member (LogObserve (LogMessage Text)) effs
    , Member ChainIndexQueryEffect effs
    )
    => RequestHandler effs ChainIndexQuery ChainIndexResponse
handleChainIndexQueries = RequestHandler $ \chainIndexQuery ->
    surroundDebug @Text "handleUtxoQueries" $ do
      case chainIndexQuery of
        DatumFromHash h            -> DatumHashResponse <$> ChainIndexEff.datumFromHash h
        ValidatorFromHash h        -> ValidatorHashResponse <$> ChainIndexEff.validatorFromHash h
        MintingPolicyFromHash h    -> MintingPolicyHashResponse <$> ChainIndexEff.mintingPolicyFromHash h
        StakeValidatorFromHash h   -> StakeValidatorHashResponse <$> ChainIndexEff.stakeValidatorFromHash h
        TxOutFromRef txOutRef      -> TxOutRefResponse <$> ChainIndexEff.txOutFromRef txOutRef
        TxFromTxId txid            -> TxIdResponse <$> ChainIndexEff.txFromTxId txid
        UtxoSetMembership txOutRef -> UtxoSetMembershipResponse <$> ChainIndexEff.utxoSetMembership txOutRef
        UtxoSetAtAddress c         -> UtxoSetAtResponse <$> ChainIndexEff.utxoSetAtAddress c
        GetTip                     -> GetTipResponse <$> ChainIndexEff.getTip

handleOwnInstanceIdQueries ::
    forall effs a.
    ( Member (LogObserve (LogMessage Text)) effs
    , Member (Reader ContractInstanceId) effs
    )
    => RequestHandler effs a ContractInstanceId
handleOwnInstanceIdQueries = RequestHandler $ \_ ->
    surroundDebug @Text "handleOwnInstanceIdQueries" ask
