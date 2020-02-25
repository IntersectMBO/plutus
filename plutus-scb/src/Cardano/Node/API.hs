{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Node.API
    ( API
    , NodeAPI
    , FollowerAPI
    , NodeFollowerAPI(..)
    ) where

import           Cardano.Node.Types        (FollowerID)
import           Control.Monad.Except      (ExceptT)
import           Control.Monad.Logger      (LoggingT)
import           Control.Monad.State       (StateT)
import           Control.Monad.Trans.Class (lift)
import           Ledger                    (Block, Slot, Tx)
import           Servant.API               ((:<|>), (:>), Capture, Get, JSON, NoContent, Post, Put, ReqBody)
import           Wallet.Emulator.Chain     (ChainEvent)

type API
     = "healthcheck" :> Get '[ JSON] NoContent
       :<|> "mempool" :> ReqBody '[ JSON] Tx :> Post '[ JSON] NoContent
       :<|> "slot" :> Get '[ JSON] Slot
       :<|> "mock" :> NodeAPI
       :<|> "follower" :> FollowerAPI

-- Routes that are not guaranteed to exist on the real node
type NodeAPI
     = "random-tx" :> Get '[ JSON] Tx
       :<|> "consume-event-history" :> Post '[ JSON] [ChainEvent]

-- Protocol 1 of the node (node followers can request new blocks)
type FollowerAPI
    = "subscribe" :> Put '[ JSON] FollowerID
        :<|> Capture "follower-id" FollowerID :> "blocks" :> Post '[ JSON] [Block]

class Monad m => NodeFollowerAPI m where
    -- FIXME names
    subscribe :: m FollowerID
    blocks :: FollowerID -> m [Block]

instance (NodeFollowerAPI m) => NodeFollowerAPI (StateT state m) where
    subscribe = lift subscribe
    blocks = lift . blocks

instance (NodeFollowerAPI m) => NodeFollowerAPI (LoggingT m) where
    subscribe = lift subscribe
    blocks = lift . blocks

instance (NodeFollowerAPI m) => NodeFollowerAPI (ExceptT e m) where
    subscribe = lift subscribe
    blocks = lift . blocks
