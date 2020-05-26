{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Protocol.Socket.API where

import           Cardano.Node.API (NodeFollowerAPI)
import           Ledger           (Block, Slot, Tx)
import           Servant.API      ((:<|>), (:>), Capture, Get, JSON, NoContent, Post, Put, ReqBody)

type API = "mempool" :> ReqBody '[ JSON] Tx :> Post '[ JSON] NoContent
      :<|> "slot"    :> Get     '[ JSON] Slot
