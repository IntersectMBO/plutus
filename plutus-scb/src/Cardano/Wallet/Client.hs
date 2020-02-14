{-# LANGUAGE TypeApplications #-}

module Cardano.Wallet.Client where

import           Cardano.Wallet.API     (API)
import           Cardano.Wallet.Types   (WalletId)
import qualified Data.ByteString.Lazy   as BSL
import           Data.Function          ((&))
import           Data.Proxy             (Proxy (Proxy))
import           Ledger                 (PubKey, Signature, Value)
import           Ledger.AddressMap      (AddressMap)
import           Network.HTTP.Client    (defaultManagerSettings, newManager)
import           Servant.Client         (ClientM, client, mkClientEnv, parseBaseUrl, runClientM)
import           Servant.Extra          (left, right)
import           Wallet.Emulator.Wallet (Wallet)

selectCoins :: WalletId -> Value -> ClientM ([Value], Value)
allocateAddress :: WalletId -> ClientM PubKey
getWatchedAddresses :: ClientM AddressMap
getWallets :: ClientM [Wallet]
getOwnPubKey :: ClientM PubKey
sign :: BSL.ByteString -> ClientM Signature
(getWallets, getOwnPubKey, sign, getWatchedAddresses, selectCoins, allocateAddress) =
    ( getWallets_
    , getOwnPubKey_
    , sign_
    , getWatchedAddresses_
    , selectCoins_
    , allocateAddress_)
  where
    api = client (Proxy @API)
    getWallets_ = api & left
    active_ = api & right & left
    getOwnPubKey_ = active_ & left
    sign_ = active_ & right & left
    getWatchedAddresses_ = active_ & right & right
    byWalletId = api & right & right
    selectCoins_ walletId = byWalletId walletId & left
    allocateAddress_ walletId = byWalletId walletId & right

main :: IO ()
main = do
    manager <- newManager defaultManagerSettings
    baseUrl <- parseBaseUrl "http://localhost:8081"
    let clientEnv = mkClientEnv manager baseUrl
        runClient = flip runClientM clientEnv
    runClient getWallets >>= print
    runClient (allocateAddress 5) >>= print
