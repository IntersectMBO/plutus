{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Cardano.Node.Client where

import           Control.Monad.Freer
import           Control.Monad.Freer.Reader          (Reader, ask)
import           Control.Monad.IO.Class
import           Data.Proxy                          (Proxy (Proxy))
import           Ledger                              (Block)
import           Ledger.TimeSlot                     (SlotConfig)
import           Servant                             (NoContent, (:<|>) (..))
import           Servant.Client                      (ClientM, client)

import           Cardano.Node.API                    (API)
import           Cardano.Node.Types                  (MockServerLogMsg)
import qualified Cardano.Protocol.Socket.Client      as Client
import qualified Cardano.Protocol.Socket.Mock.Client as MockClient
import           Control.Monad.Freer.Extras.Log      (LogMessage)
import           Wallet.Effects                      (NodeClientEffect (..))

healthcheck :: ClientM NoContent
consumeEventHistory :: ClientM [LogMessage MockServerLogMsg]
(healthcheck, consumeEventHistory) =
    ( healthcheck_
    , consumeEventHistory_
    )
  where
    healthcheck_ :<|> consumeEventHistory_ =
        client (Proxy @API)

handleNodeClientClient ::
    forall m effs.
    ( LastMember m effs
    , MonadIO m
    , Member (Reader MockClient.TxSendHandle) effs
    , Member (Reader ChainSyncHandle) effs
    )
    => SlotConfig
    -> NodeClientEffect
    ~> Eff effs
handleNodeClientClient slotCfg e = do
    txSendHandle <- ask @MockClient.TxSendHandle
    chainSyncHandle <- ask @ChainSyncHandle
    case e of
        PublishTx tx  -> liftIO $ MockClient.queueTx txSendHandle tx
        GetClientSlot ->
            either (liftIO . MockClient.getCurrentSlot) (liftIO . Client.getCurrentSlot) chainSyncHandle
        GetClientSlotConfig -> pure slotCfg

type ChainSyncHandle = Either (Client.ChainSyncHandle Block) (Client.ChainSyncHandle Client.ChainSyncEvent)
