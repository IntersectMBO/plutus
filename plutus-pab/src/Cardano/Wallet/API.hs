{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Wallet.API
    ( API
    ) where

import           Ledger            (PubKey, Value)
import           Ledger.AddressMap (UtxoMap)
import           Ledger.Slot       (Slot)
import           Ledger.Tx         (Tx)
import           Servant.API       (Get, JSON, NoContent, Post, ReqBody, (:<|>), (:>))
import           Wallet.Effects    (Payment)

type API
    = "submit-txn" :> ReqBody '[JSON] Tx :> Post '[JSON] NoContent
      :<|> "own-public-key" :> Get '[JSON] PubKey
      :<|> "update-payment-with-change" :> ReqBody '[JSON] (Value, Payment) :> Post '[JSON] Payment
      :<|> "wallet-slot" :> Get '[JSON] Slot
      :<|> "own-outputs" :> Get '[JSON] UtxoMap
