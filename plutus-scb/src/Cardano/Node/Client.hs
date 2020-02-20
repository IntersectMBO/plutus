{-# LANGUAGE TypeApplications #-}

module Cardano.Node.Client where

import           Cardano.Node.API      (API)
import           Data.Map              (Map)
import           Data.Proxy            (Proxy (Proxy))
import           Ledger                (Address, Blockchain, Slot, Tx, TxOut, TxOutRef)
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
(healthcheck, addTx, getCurrentSlot, randomTx, utxoAt, blockchain, consumeEventHistory) =
    ( healthcheck_
    , addTx_
    , getCurrentSlot_
    , randomTx_
    , utxoAt_
    , blockchain_
    , consumeEventHistory_)
  where
    healthcheck_ :<|> addTx_ :<|> getCurrentSlot_ :<|> (randomTx_ :<|> utxoAt_ :<|> blockchain_ :<|> consumeEventHistory_) =
        client (Proxy @API)
