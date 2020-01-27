{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Wallet.API
    ( API
    ) where

import           Cardano.Wallet.Types   (WalletId)
import           Ledger                 (PubKey, Value)
import           Servant.API            ((:<|>), (:>), Capture, Get, JSON, Post, ReqBody)
import           Wallet.Emulator.Wallet (Wallet)

type API
     = "wallets" :> (Get '[ JSON] [Wallet]
                     :<|> (Capture "walletId" WalletId :> ("coin-selections" :> "random" :> ReqBody '[ JSON] Value :> Get '[ JSON] ( [Value]
                                                                                                                                   , Value)
                                                           :<|> "addresses" :> "new" :> Post '[ JSON] PubKey)))
