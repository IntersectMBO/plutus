{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Node.API
    ( API
    ) where

import           Ledger      (Slot, Tx)
import           Servant.API ((:<|>), (:>), Get, JSON, NoContent, Post, ReqBody)

type API
     = "healthcheck" :> Get '[ JSON] NoContent
       :<|> "mempool" :> ReqBody '[ JSON] Tx :> Post '[ JSON] NoContent
       :<|> "slot" :> Get '[ JSON] Slot
       :<|> "random-tx" :> Get '[ JSON] Tx
