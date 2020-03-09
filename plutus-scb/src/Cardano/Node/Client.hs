{-# LANGUAGE TypeApplications #-}

module Cardano.Node.Client where

import           Cardano.Node.API      (API)
import           Cardano.Node.Types    (FollowerID)
import           Data.Map              (Map)
import           Data.Proxy            (Proxy (Proxy))
import           Ledger                (Address, Block, Blockchain, Slot, Tx, TxOut, TxOutRef)
import           Servant               ((:<|>) (..), NoContent)
import           Servant.Client        (ClientM, client)
import           Wallet.Emulator.Chain (ChainEvent)

healthcheck :: ClientM NoContent
getCurrentSlot :: ClientM Slot
addTx :: Tx -> ClientM NoContent
randomTx :: ClientM Tx
utxoAt :: Address -> ClientM (Map TxOutRef TxOut)
blockchain :: ClientM Blockchain
consumeEventHistory :: ClientM [ChainEvent]
newFollower :: ClientM FollowerID
getBlocks :: FollowerID -> ClientM [Block]
(healthcheck, addTx, getCurrentSlot, randomTx, utxoAt, blockchain, consumeEventHistory, newFollower, getBlocks) =
    ( healthcheck_
    , addTx_
    , getCurrentSlot_
    , randomTx_
    , utxoAt_
    , blockchain_
    , consumeEventHistory_
    , newFollower_
    , getBlocks_
    )
  where
    healthcheck_ :<|> addTx_ :<|> getCurrentSlot_ :<|> (randomTx_ :<|> utxoAt_ :<|> blockchain_ :<|> consumeEventHistory_) :<|> (newFollower_ :<|> getBlocks_) =
        client (Proxy @API)
