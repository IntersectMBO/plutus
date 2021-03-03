{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Node.Client where

import           Control.Monad                  (void)
import           Control.Monad.Freer
import           Control.Monad.IO.Class
import           Data.Proxy                     (Proxy (Proxy))
import           Ledger                         (Slot, Tx)
import           Servant                        (NoContent, (:<|>) (..))
import           Servant.Client                 (ClientEnv, ClientError, ClientM, client, runClientM)

import           Cardano.Node.API               (API)
import           Cardano.Node.RandomTx          (GenRandomTx (..))
import           Cardano.Node.Types             (MockServerLogMsg)
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Extras.Log (LogMessage)
import           Wallet.Effects                 (NodeClientEffect (..))

healthcheck :: ClientM NoContent
getCurrentSlot :: ClientM Slot
addTx :: Tx -> ClientM NoContent
randomTx :: ClientM Tx
consumeEventHistory :: ClientM [LogMessage MockServerLogMsg]
(healthcheck, addTx, getCurrentSlot, randomTx, consumeEventHistory) =
    ( healthcheck_
    , addTx_
    , getCurrentSlot_
    , randomTx_
    , consumeEventHistory_
    )
  where
    healthcheck_ :<|> addTx_ :<|> getCurrentSlot_ :<|> (randomTx_ :<|> consumeEventHistory_) =
        client (Proxy @API)

handleRandomTxClient ::
    forall m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Error ClientError) effs)
    => ClientEnv
    -> GenRandomTx
    ~> Eff effs
handleRandomTxClient clientEnv =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
    in \case
        GenRandomTx -> runClient randomTx

handleNodeClientClient ::
    forall m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Error ClientError) effs
    )
    => ClientEnv
    -> NodeClientEffect
    ~> Eff effs
handleNodeClientClient clientEnv =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
    in \case
        PublishTx tx  -> void (runClient (addTx tx))
        GetClientSlot -> runClient getCurrentSlot
