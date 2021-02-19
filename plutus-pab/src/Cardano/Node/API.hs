{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Node.API
    ( API
    , NodeAPI
    , FollowerAPI
    ) where

import           Servant.API                    (Capture, Get, JSON, NoContent, Post, Put, ReqBody, (:<|>), (:>))

import           Cardano.Node.Types             (FollowerID, MockServerLogMsg)
import           Control.Monad.Freer.Extras.Log (LogMessage)
import           Ledger                         (Block, Slot, Tx)

type API
     = "healthcheck" :> Get '[ JSON] NoContent
       :<|> "mempool" :> ReqBody '[ JSON] Tx :> Post '[ JSON] NoContent
       :<|> "slot" :> Get '[ JSON] Slot
       :<|> "mock" :> NodeAPI
       :<|> "follower" :> FollowerAPI

-- Routes that are not guaranteed to exist on the real node
type NodeAPI
     = "random-tx" :> Get '[ JSON] Tx
       :<|> "consume-event-history" :> Post '[ JSON] [LogMessage MockServerLogMsg]

-- Protocol 1 of the node (node followers can request new blocks)
type FollowerAPI
    = "subscribe" :> Put '[ JSON] FollowerID
        :<|> Capture "follower-id" FollowerID :> "blocks" :> Post '[ JSON] [Block]
