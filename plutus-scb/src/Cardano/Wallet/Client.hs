{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Wallet.Client where

import           Cardano.Wallet.API        (API)
import           Cardano.Wallet.Types      (WalletId)
import           Control.Lens
import           Control.Monad.Freer
import           Control.Monad.Freer.Error (Error, throwError)
import           Control.Monad.IO.Class    (MonadIO (..))
import           Data.Proxy                (Proxy (Proxy))
import           Ledger                    (Address, PubKey, TxOutRef, Value, pubKeyAddress)
import           Ledger.AddressMap         (AddressMap, UtxoMap, fundsAt)
import           Servant                   (NoContent)
import           Servant.Client            (ClientEnv, ClientError, ClientM, client, runClientM)
import           Servant.Extra             (left, right)
import           Wallet.API                (WalletAPIError)
import           Wallet.Effects            (NodeClientEffect, WalletEffect (..), getClientSlot, publishTx)
import           Wallet.Emulator.Wallet    (Payment (..), PaymentArgs (..), Wallet, handleUpdatePaymentWithChange)

selectCoins :: WalletId -> Value -> ClientM ([(TxOutRef, Value)], Value)
allocateAddress :: WalletId -> ClientM PubKey
getWatchedAddresses :: ClientM AddressMap
getWallets :: ClientM [Wallet]
getOwnPubKey :: ClientM PubKey
startWatching :: Address -> ClientM NoContent
valueAt :: Address -> ClientM Value
(getWallets, getOwnPubKey, getWatchedAddresses, startWatching, selectCoins, allocateAddress, valueAt) =
    ( getWallets_
    , getOwnPubKey_
    , getWatchedAddresses_
    , startWatching_
    , selectCoins_
    , allocateAddress_
    , valueAt_)
  where
    api = client (Proxy @API)
    getWallets_ = api & left
    getOwnPubKey_ = api & right & left
    getWatchedAddresses_ = api & right & right & left
    startWatching_ = api & right & right & right & left
    byWalletId = api & right & right & right & right & left
    selectCoins_ walletId = byWalletId walletId & left
    allocateAddress_ walletId = byWalletId walletId & right
    valueAt_ = api & right & right & right & right & right

getOwnOutputs :: ClientM UtxoMap
getOwnOutputs = do
    pk <- getOwnPubKey
    am <- getWatchedAddresses
    pure $ am ^. fundsAt (pubKeyAddress pk)

handleWalletClient ::
  forall m effs.
  ( LastMember m effs
  , MonadIO m
  , Member NodeClientEffect effs
  , Member (Error WalletAPIError) effs
  , Member (Error ClientError) effs
  )
  => ClientEnv
  -> Eff (WalletEffect ': effs)
  ~> Eff effs
handleWalletClient clientEnv =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
    in
      interpret $ \case
        SubmitTxn t -> publishTx t
        OwnPubKey -> runClient getOwnPubKey
        UpdatePaymentWithChange vl (oldIns, changeOut) -> do
            utxo <- runClient getWatchedAddresses
            pubK <- runClient getOwnPubKey
            let ownAddress = pubKeyAddress pubK
                args   = PaymentArgs
                            { availableFunds = utxo ^. fundsAt ownAddress
                            , ownPubKey = pubK
                            , requestedValue = vl
                            }
                pmt    = Payment{paymentInputs = oldIns, paymentChangeOutput = changeOut}
            Payment{paymentInputs, paymentChangeOutput} <- handleUpdatePaymentWithChange args pmt
            pure (paymentInputs, paymentChangeOutput)
        WalletSlot -> getClientSlot
        OwnOutputs -> do
            pubK <- runClient getOwnPubKey
            let ownAddress = pubKeyAddress pubK
            view (at ownAddress . non mempty) <$> runClient getWatchedAddresses
