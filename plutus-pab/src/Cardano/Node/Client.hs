{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Node.Client where

import           Cardano.Node.API          (API)
import           Cardano.Node.Follower     (NodeFollowerEffect (..))
import           Cardano.Node.RandomTx     (GenRandomTx (..))
import           Cardano.Node.Types        (FollowerID)
import           Control.Monad             (void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Log   (LogMessage)
import           Control.Monad.IO.Class
import           Data.Proxy                (Proxy (Proxy))
import           Ledger                    (Block, Slot, Tx)
import           Servant                   (NoContent, (:<|>) (..))
import           Servant.Client            (ClientEnv, ClientError, ClientM, client, runClientM)
import           Wallet.Effects            (NodeClientEffect (..))
import           Wallet.Emulator.Chain     (ChainEvent)

healthcheck :: ClientM NoContent
getCurrentSlot :: ClientM Slot
addTx :: Tx -> ClientM NoContent
randomTx :: ClientM Tx
consumeEventHistory :: ClientM [LogMessage ChainEvent]
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
    -> Eff (NodeFollowerEffect ': effs)
    ~> Eff effs
handleNodeFollowerClient clientEnv =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure in
    interpret $ \case
    NewFollower   -> runClient newFollower
    GetBlocks fid -> runClient (getBlocks fid)
    GetSlot       -> runClient getCurrentSlot

handleRandomTxClient ::
    forall m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Error ClientError) effs)
    => ClientEnv
    -> Eff (GenRandomTx ': effs)
    ~> Eff effs
handleRandomTxClient clientEnv =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure in
    interpret $ \case
        GenRandomTx -> runClient randomTx

handleNodeClientClient ::
    forall m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Error ClientError) effs
    )
    => ClientEnv
    -> Eff (NodeClientEffect ': effs)
    ~> Eff effs
handleNodeClientClient clientEnv =
    let
        runClient :: forall a. ClientM a -> Eff effs a
        runClient a = (sendM $ liftIO $ runClientM a clientEnv) >>= either throwError pure in
    interpret $ \case
        PublishTx tx  -> void (runClient (addTx tx))
        GetClientSlot -> runClient getCurrentSlot
