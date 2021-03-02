{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Node.API
    ( API
    , NodeAPI
    ) where

import           Servant.API                    (Get, JSON, NoContent, Post, (:<|>), (:>))

import           Cardano.Node.Types             (MockServerLogMsg)
import           Control.Monad.Freer.Extras.Log (LogMessage)
import           Ledger                         (Slot, Tx)

type API
     = "healthcheck" :> Get '[ JSON] NoContent
       :<|> "slot" :> Get '[ JSON] Slot
       :<|> "mock" :> NodeAPI

-- Routes that are not guaranteed to exist on the real node
type NodeAPI
     = "random-tx" :> Get '[ JSON] Tx
       :<|> "consume-event-history" :> Post '[ JSON] [LogMessage MockServerLogMsg]
