{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Wallet.API
    ( API
    ) where

import           Ledger                 (PubKey, Value)
import           Ledger.AddressMap      (UtxoMap)
import           Ledger.Slot            (Slot)
import           Ledger.Tx              (Tx)
import           Servant.API            (Capture, Get, JSON, NoContent, Post, ReqBody, (:<|>), (:>))
import           Wallet.Effects         (Payment)
import           Wallet.Emulator.Wallet (Wallet)


type API
    = "create" :> Post '[JSON] Wallet
      :<|> Capture "walletId" Integer :> "submit-txn" :> ReqBody '[JSON] Tx :> Post '[JSON] NoContent
      :<|> Capture "walletId" Integer :> "own-public-key" :> Get '[JSON] PubKey
      :<|> Capture "walletId" Integer :> "update-payment-with-change" :> ReqBody '[JSON] (Value, Payment) :> Post '[JSON] Payment
      :<|> Capture "walletId" Integer :> "wallet-slot" :> Get '[JSON] Slot
      :<|> Capture "walletId" Integer :> "own-outputs" :> Get '[JSON] UtxoMap
      :<|> Capture "walletId" Integer :> "total-funds" :> Get '[JSON] Value
      :<|> Capture "walletId" Integer :> "sign" :> ReqBody '[JSON] Tx :> Post '[JSON] Tx
