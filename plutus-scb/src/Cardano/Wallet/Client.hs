{-# LANGUAGE TypeApplications #-}

module Cardano.Wallet.Client where

import           Cardano.Wallet.API     (API)
import           Cardano.Wallet.Types   (WalletId)
import           Data.Function          ((&))
import           Data.Proxy             (Proxy (Proxy))
import           Ledger                 (PubKey, Value)
import           Network.HTTP.Client    (defaultManagerSettings, newManager)
import           Servant.Client         (ClientM, client, mkClientEnv, parseBaseUrl, runClientM)
import           Servant.Extra          (left, right)
import           Wallet.Emulator.Wallet (Wallet)

selectCoins :: WalletId -> Value -> ClientM ([Value], Value)
allocateAddress :: WalletId -> ClientM PubKey
getWallets :: ClientM [Wallet]
(getWallets, selectCoins, allocateAddress) =
    (getWallets_, selectCoins_, allocateAddress_)
  where
    api = client (Proxy @API)
    getWallets_ = left api
    selectCoins_ walletId = right api walletId & left
    allocateAddress_ walletId = right api walletId & right

main :: IO ()
main = do
    manager <- newManager defaultManagerSettings
    baseUrl <- parseBaseUrl "http://localhost:8081"
    let clientEnv = mkClientEnv manager baseUrl
        runClient = flip runClientM clientEnv
    runClient getWallets >>= print
    runClient (allocateAddress 5) >>= print
