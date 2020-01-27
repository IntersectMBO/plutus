{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Node.API
    ( API
    ) where

import           Ledger      (Slot)
import           Servant.API ((:<|>), (:>), Get, JSON, NoContent, Put)

type API
     = "healthcheck" :> Get '[ JSON] NoContent
       :<|> "block" :> (Get '[ JSON] Slot
                        :<|> "add" :> Put '[ JSON] Slot)
