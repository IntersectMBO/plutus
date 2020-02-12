{-# LANGUAGE TypeApplications #-}

module Cardano.Node.Client where

import           Cardano.Node.API    (API)
import           Data.Proxy          (Proxy (Proxy))
import           Ledger              (Slot, Tx)
import           Network.HTTP.Client (defaultManagerSettings, newManager)
import           Servant             (NoContent, (:<|>)(..))
import           Servant.Client      (ClientM, client, mkClientEnv, parseBaseUrl, runClientM)

healthcheck :: ClientM NoContent
getCurrentSlot :: ClientM Slot
addTx :: Tx -> ClientM NoContent
(healthcheck, addTx, getCurrentSlot) =
    (healthcheck_, addTx_, getCurrentSlot_)
  where
    healthcheck_ :<|> addTx_ :<|> getCurrentSlot_ = client (Proxy @API)
    
main :: IO ()
main = do
    manager <- newManager defaultManagerSettings
    baseUrl <- parseBaseUrl "http://localhost:8082"
    let clientEnv = mkClientEnv manager baseUrl
        runClient = flip runClientM clientEnv
    putStrLn "Get slot"
    runClient getCurrentSlot >>= print
