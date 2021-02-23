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
import           Servant                        (NoContent, (:<|>) (..))
import           Servant.Client                 (ClientEnv, ClientError, ClientM, client, runClientM)

import           Cardano.Node.API               (API)
import           Cardano.Node.RandomTx          (GenRandomTx (..))
import           Cardano.Node.Types             (FollowerID, MockServerLogMsg, NodeFollowerEffect (..))
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Extras.Log (LogMessage)
import           Ledger                         (Block, Slot, Tx)
import           Wallet.Effects                 (NodeClientEffect (..))

healthcheck :: ClientM NoContent
getCurrentSlot :: ClientM Slot
addTx :: Tx -> ClientM NoContent
randomTx :: ClientM Tx
consumeEventHistory :: ClientM [LogMessage MockServerLogMsg]
newFollower :: ClientM FollowerID
getBlocks :: FollowerID -> ClientM [Block]
(healthcheck, addTx, getCurrentSlot, randomTx, consumeEventHistory, newFollower, getBlocks) =
    ( healthcheck_
    , addTx_
    , getCurrentSlot_
    , randomTx_
    , consumeEventHistory_
    , newFollower_
    , getBlocks_
    )
  where
    healthcheck_ :<|> addTx_ :<|> getCurrentSlot_ :<|> (randomTx_ :<|> consumeEventHistory_) :<|> (newFollower_ :<|> getBlocks_) =
        client (Proxy @API)

handleNodeFollowerClient ::
    forall m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Error ClientError) effs)
    => ClientEnv
    -> NodeFollowerEffect
    ~> Eff effs
handleNodeFollowerClient clientEnv =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure
    in \case
        NewFollower   -> runClient newFollower
        GetBlocks fid -> runClient (getBlocks fid)
        GetSlot       -> runClient getCurrentSlot

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
