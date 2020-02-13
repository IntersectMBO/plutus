{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Wallet.API
    ( API
    ) where

import           Cardano.Wallet.Types   (WalletId)
import qualified Data.ByteString.Lazy      as BSL
import           Ledger                 (PubKey, Value,Signature)
import           Servant.API            ((:<|>), (:>), Capture, Get, JSON, Post, ReqBody)
import           Wallet.Emulator.Wallet (Wallet)

-- | Note: This API uses the wholly-fictitious notion of an "active" wallet.
-- This is purely to fit in easily with the 'WalletAPI's 'ownPubKey'
-- call, which assumes there is a single public key we own. This will
-- have to be revisited later.
type API
     = "wallets" :> (Get '[ JSON] [Wallet]
                     :<|> "active" :> "pubkey" :> Get '[ JSON] PubKey
                     :<|> "active" :> "sign" :> ReqBody '[JSON] BSL.ByteString :> Post '[ JSON] Signature
                     :<|> (Capture "walletId" WalletId :> ("coin-selections" :> "random" :> ReqBody '[ JSON] Value :> Get '[ JSON] ( [Value]
                                                                                                                                   , Value)
                                                           :<|> "addresses" :> "new" :> Post '[ JSON] PubKey)))
