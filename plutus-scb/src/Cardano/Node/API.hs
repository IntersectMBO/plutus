{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Node.API
    ( API
    ) where

import           Data.Map              (Map)

import           Cardano.Node.Types    (FollowerID)
import           Ledger                (Address, Block, Blockchain, Slot, Tx, TxOut, TxOutRef)
import           Servant.API           ((:<|>), (:>), Capture, Get, JSON, NoContent, Post, Put, ReqBody)
import           Wallet.Emulator.Chain (ChainEvent)

type API
     = "healthcheck" :> Get '[ JSON] NoContent
       :<|> "mempool" :> ReqBody '[ JSON] Tx :> Post '[ JSON] NoContent
       :<|> "slot" :> Get '[ JSON] Slot
       :<|> "mock" :> MockAPI
       :<|> "follower" :> FollowerAPI

-- Routes that are not guaranteed to exist on the real node
type MockAPI
     = "random-tx" :> Get '[ JSON] Tx
       :<|> "utxo-at" :> ReqBody '[ JSON] Address :> Post '[ JSON] (Map TxOutRef TxOut)
       :<|> "blockchain" :> Get '[ JSON] Blockchain -- TODO: This should be replaced by the followe API
       :<|> "consume-event-history" :> Post '[ JSON] [ChainEvent]

-- Protocol 1 of the node (node followers can request new blocks)
type FollowerAPI
    = "add" :> Put '[ JSON] FollowerID
        :<|> Capture "follower-id" FollowerID :> "blocks" :> Post '[ JSON] [Block]
