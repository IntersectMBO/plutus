{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module ContractServer
    ( serveContract
    ) where

import qualified Servant.Server           as Servant
import           Data.Proxy               (Proxy)
import           Network.Wai.Handler.Warp (run)
import           Text.Read                (readMaybe)
import           System.Environment       (getArgs, lookupEnv)
import           Control.Monad            (mplus)
import           Data.Maybe               (fromMaybe)
import           Language.Plutus.Contract.Servant (contractApp)
import           Network.Wai (Application)
import           Network.Wai.Handler.Warp (run)
import           Language.Plutus.Contract          (PlutusContract)

defaultPort :: Int
defaultPort = 16523 -- 408B

envName :: String
envName = "PLUTUS_CONTRACT_HTTP_PORT"

findPort :: IO Int
findPort = do
  args <- getArgs
  let argsPort :: Maybe Int
      argsPort = case args of
                   [port] -> readMaybe port
                   _      -> Nothing
  envPort <- (>>= readMaybe) <$> lookupEnv envName
  pure $ fromMaybe defaultPort (argsPort `mplus` envPort)

serveHTTP :: Application -> IO ()
serveHTTP app = do
  port <- findPort
  putStrLn $ envName ++ ": " ++ show port
  run port app

serveContract :: PlutusContract () -> IO ()
serveContract contract = serveHTTP (contractApp contract)
