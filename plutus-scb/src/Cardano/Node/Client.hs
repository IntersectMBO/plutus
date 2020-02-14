{-# LANGUAGE TypeApplications #-}

module Cardano.Node.Client where

import           Cardano.Node.API    (API)
import           Data.Map            (Map)
import           Data.Proxy          (Proxy (Proxy))
import           Ledger              (Address, Slot, Tx, TxOut, TxOutRef)
import           Network.HTTP.Client (defaultManagerSettings, newManager)
import           Servant             ((:<|>) (..), NoContent)
import           Servant.Client      (ClientM, client, mkClientEnv, parseBaseUrl, runClientM)

healthcheck :: ClientM NoContent
getCurrentSlot :: ClientM Slot
addTx :: Tx -> ClientM NoContent
randomTx :: ClientM Tx
utxoAt :: Address -> ClientM (Map TxOutRef TxOut)
(healthcheck, addTx, getCurrentSlot, randomTx, utxoAt) =
    (healthcheck_, addTx_, getCurrentSlot_, randomTx_, utxoAt_)
  where
    healthcheck_ :<|> addTx_ :<|> getCurrentSlot_ :<|> (randomTx_ :<|> utxoAt_) =
        client (Proxy @API)

main :: IO ()
main = do
    manager <- newManager defaultManagerSettings
    baseUrl <- parseBaseUrl "http://localhost:8082"
    let clientEnv = mkClientEnv manager baseUrl
        runClient = flip runClientM clientEnv
    putStrLn "Get slot"
    runClient getCurrentSlot >>= print
