{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Node.API
    ( API
    ) where

import           Data.Map              (Map)

import           Ledger                (Address, Blockchain, Slot, Tx, TxOut, TxOutRef)
import           Servant.API           ((:<|>), (:>), Get, JSON, NoContent, Post, ReqBody)
import           Wallet.Emulator.Chain (ChainEvent)

type API
     = "healthcheck" :> Get '[ JSON] NoContent
       :<|> "mempool" :> ReqBody '[ JSON] Tx :> Post '[ JSON] NoContent
       :<|> "slot" :> Get '[ JSON] Slot
       :<|> "mock" :> MockAPI

-- Routes that are not guaranteed to exist on the real node
type MockAPI
     = "random-tx" :> Get '[ JSON] Tx
       :<|> "utxo-at" :> ReqBody '[ JSON] Address :> Post '[ JSON] (Map TxOutRef TxOut)
       :<|> "blockchain" :> Get '[ JSON] Blockchain
       :<|> "consume-event-history" :> Post '[ JSON] [ChainEvent]
