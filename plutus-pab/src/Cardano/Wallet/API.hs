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
      :<|> Capture "walletId" Wallet :> "submit-txn" :> ReqBody '[JSON] Tx :> Post '[JSON] NoContent
      :<|> Capture "walletId" Wallet :> "own-public-key" :> Get '[JSON] PubKey
      :<|> Capture "walletId" Wallet :> "update-payment-with-change" :> ReqBody '[JSON] (Value, Payment) :> Post '[JSON] Payment
      :<|> Capture "walletId" Wallet :> "wallet-slot" :> Get '[JSON] Slot
      :<|> Capture "walletId" Wallet :> "own-outputs" :> Get '[JSON] UtxoMap
      :<|> Capture "walletId" Wallet :> "total-funds" :> Get '[JSON] Value
      :<|> Capture "walletId" Wallet :> "sign" :> ReqBody '[JSON] Tx :> Post '[JSON] Tx
