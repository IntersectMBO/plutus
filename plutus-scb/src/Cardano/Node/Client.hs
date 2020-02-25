{-# LANGUAGE TypeApplications #-}

module Cardano.Node.Client where

import           Cardano.Node.API      (API)
import           Cardano.Node.Types    (FollowerID)
import           Data.Proxy            (Proxy (Proxy))
import           Ledger                (Block, Slot, Tx)
import           Servant               ((:<|>) (..), NoContent)
import           Servant.Client        (ClientM, client)
import           Wallet.Emulator.Chain (ChainEvent)

healthcheck :: ClientM NoContent
getCurrentSlot :: ClientM Slot
addTx :: Tx -> ClientM NoContent
randomTx :: ClientM Tx
consumeEventHistory :: ClientM [ChainEvent]
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
