{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.ChainIndex.Client where

import           Cardano.ChainIndex.API    (API)
import           Control.Monad             (void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error (Error, throwError)
import           Control.Monad.IO.Class    (MonadIO (..))
import           Data.Proxy                (Proxy (Proxy))
import           Ledger                    (Address, TxId)
import           Ledger.AddressMap         (AddressMap)
import           Servant                   ((:<|>) (..), NoContent)
import           Servant.Client            (ClientEnv, ClientError, ClientM, client, runClientM)

import           Wallet.Effects            (ChainIndexEffect (..))

healthCheck :: ClientM NoContent
startWatching :: Address -> ClientM NoContent
watchedAddresses :: ClientM AddressMap
transactionConfirmed :: TxId -> ClientM Bool
(healthCheck, startWatching, watchedAddresses, transactionConfirmed) =
  (healthCheck_, startWatching_, watchedAddresses_, txConfirmed_)
  where
    healthCheck_ :<|> startWatching_ :<|> watchedAddresses_ :<|> txConfirmed_  =
        client (Proxy @API)

handleChainIndexClient ::
  forall m effs.
  ( LastMember m effs
  , MonadIO m
  , Member (Error ClientError) effs)
  => ClientEnv
  -> Eff (ChainIndexEffect ': effs)
  ~> Eff effs
handleChainIndexClient clientEnv =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
    in
      interpret $ \case
        StartWatching a -> void (runClient (startWatching a))
        WatchedAddresses -> runClient watchedAddresses
        TransactionConfirmed txid -> runClient (transactionConfirmed txid)
