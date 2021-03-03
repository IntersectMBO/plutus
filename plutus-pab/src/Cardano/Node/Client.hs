{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Node.Client where

import           Control.Monad.Freer
import           Control.Monad.IO.Class
import           Data.Proxy                     (Proxy (Proxy))
import           Ledger                         (Tx)
import           Servant                        (NoContent, (:<|>) (..))
import           Servant.Client                 (ClientEnv, ClientError, ClientM, client, runClientM)

import           Cardano.Node.API               (API)
import           Cardano.Node.RandomTx          (GenRandomTx (..))
import           Cardano.Node.Types             (MockServerLogMsg)
import qualified Cardano.Protocol.Socket.Client as Client
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Extras.Log (LogMessage)
import           Wallet.Effects                 (NodeClientEffect (..))

healthcheck :: ClientM NoContent
randomTx :: ClientM Tx
consumeEventHistory :: ClientM [LogMessage MockServerLogMsg]
(healthcheck, randomTx, consumeEventHistory) =
    ( healthcheck_
    , randomTx_
    , consumeEventHistory_
    )
  where
    healthcheck_ :<|> (randomTx_ :<|> consumeEventHistory_) =
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
    )
    => Client.ClientHandler
    -> NodeClientEffect
    ~> Eff effs
handleNodeClientClient clientHandler = \case
    PublishTx tx  ->
        liftIO $ Client.queueTx clientHandler tx
    GetClientSlot ->
        liftIO $ Client.getCurrentSlot clientHandler
