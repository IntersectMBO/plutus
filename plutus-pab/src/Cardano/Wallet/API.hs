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

{- Note [WalletID type in wallet API]

We use the following type to identify wallets:

@newtype Wallet = Wallet Integer@

This creates two problems for the purescript bridge:

1. We need to use a bigint library in Purescript. This is done in
'PSGenerator.Common.integerBridge'. Technically, JSON numbers have no size
limit, but we need the special library for parsing (I think!)
2. Sometimes we want to use 'Wallet' as part of a URL. Normally we would do
this in servant with 'Capture "walletId" Wallet'. But this is going to break
the purescript bridge that generates the API client, because it can't handle
'Wallet' or even 'Integer' types.
To address this, we parameterise the API over the type of wallet ID. In the
servant server implementation we specialise this to 'Integer'. In the
PSGenerator we specialise it to 'Text'.

-}

type API walletId -- see note [WalletID type in wallet API]
    = "create" :> Post '[JSON] Wallet
      :<|> Capture "walletId" walletId :> "submit-txn" :> ReqBody '[JSON] Tx :> Post '[JSON] NoContent
      :<|> Capture "walletId" walletId :> "own-public-key" :> Get '[JSON] PubKey
      :<|> Capture "walletId" walletId :> "update-payment-with-change" :> ReqBody '[JSON] (Value, Payment) :> Post '[JSON] Payment
      :<|> Capture "walletId" walletId :> "wallet-slot" :> Get '[JSON] Slot
      :<|> Capture "walletId" walletId :> "own-outputs" :> Get '[JSON] UtxoMap
      :<|> Capture "walletId" walletId :> "total-funds" :> Get '[JSON] Value
      :<|> Capture "walletId" walletId :> "sign" :> ReqBody '[JSON] Tx :> Post '[JSON] Tx
