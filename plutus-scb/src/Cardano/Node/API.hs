{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Node.API
    ( API
    ) where

import           Ledger      (Tx, Slot)
import           Servant.API ((:<|>), (:>), Get, JSON, NoContent, ReqBody, Post)

type API
     = "healthcheck" :> Get '[ JSON] NoContent
       :<|> "mempool" :> ReqBody '[ JSON] Tx :> Post '[ JSON] NoContent
       :<|> "slot" :> Get '[ JSON] Slot
       :<|> "random-tx" :> Get '[ JSON] Tx
