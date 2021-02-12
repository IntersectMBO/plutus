{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Wallet.API
    ( API
    ) where

import           Cardano.Wallet.Types
import           Ledger               (PubKey, Value)
import           Ledger.AddressMap    (UtxoMap)
import           Ledger.Slot          (Slot)
import           Ledger.Tx            (Tx)
import           Servant.API          (Capture, Get, JSON, NoContent, Post, ReqBody, (:<|>), (:>))
import           Wallet.Effects       (Payment)

type API
    = Capture "walletId" WalletId :> "submit-txn" :> ReqBody '[JSON] Tx :> Post '[JSON] NoContent
      :<|> Capture "walletId" WalletId :> "own-public-key" :> Get '[JSON] PubKey
      :<|> Capture "walletId" WalletId :> "update-payment-with-change" :> ReqBody '[JSON] (Value, Payment) :> Post '[JSON] Payment
      :<|> Capture "walletId" WalletId :> "wallet-slot" :> Get '[JSON] Slot
      :<|> Capture "walletId" WalletId :> "own-outputs" :> Get '[JSON] UtxoMap
