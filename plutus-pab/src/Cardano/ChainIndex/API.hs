{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.ChainIndex.API where

import           Ledger            (Address, TxId)
import           Ledger.AddressMap (AddressMap)
import           Ledger.Blockchain (Block)
import           Servant.API       (Get, JSON, NoContent, Post, ReqBody, (:<|>), (:>))
import           Wallet.Effects    (AddressChangeRequest, AddressChangeResponse)

type API
     = "healthcheck" :> Get '[ JSON] NoContent
     :<|> "start-watching" :> ReqBody '[ JSON] Address :> Post '[ JSON] NoContent
     :<|> "watched-addresses" :> Get '[ JSON] AddressMap
     :<|> "confirmed-blocks" :> Get '[ JSON] [Block]
     :<|> "transaction-confirmed" :> ReqBody '[ JSON] TxId :> Post '[ JSON] Bool
     :<|> "next-tx" :> ReqBody '[ JSON] AddressChangeRequest :> Post '[ JSON] AddressChangeResponse
