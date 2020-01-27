{-# LANGUAGE TypeApplications #-}

module Cardano.Node.Client where

import           Cardano.Node.API    (API)
import           Data.Function       ((&))
import           Data.Proxy          (Proxy (Proxy))
import           Ledger              (Slot)
import           Network.HTTP.Client (defaultManagerSettings, newManager)
import           Servant             (NoContent)
import           Servant.Client      (ClientM, client, mkClientEnv, parseBaseUrl, runClientM)
import           Servant.Extra       (left, right)

healthcheck :: ClientM NoContent
getCurrentSlot :: ClientM Slot
addBlock :: ClientM Slot
(healthcheck, getCurrentSlot, addBlock) =
    (healthcheck_, getCurrentSlot_, addBlock_)
  where
    api = client (Proxy @API)
    healthcheck_ = left api
    getCurrentSlot_ = right api & left
    addBlock_ = right api & right

main :: IO ()
main = do
    manager <- newManager defaultManagerSettings
    baseUrl <- parseBaseUrl "http://localhost:8082"
    let clientEnv = mkClientEnv manager baseUrl
        runClient = flip runClientM clientEnv
    putStrLn "Get slot"
    runClient getCurrentSlot >>= print
