{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Main where

import Data.Proxy
import Network.HTTP.Client (newManager, defaultManagerSettings)
import Servant.API
import Servant.Client
import GHC.Generics     (Generic)
import Data.Aeson.Types (FromJSON, ToJSON)
import Data.Map
import Language.Marlowe.ACTUS.Definitions.ContractTerms

data ModelInput = ModelInput {
    ct :: ContractTerms
    , rf :: Map String (Map String Double)
    }
    deriving stock (Show, Generic) 
    deriving ToJSON


data Payoff = Payoff {
    event :: String
    , payoff :: Double
    }
    deriving stock (Show, Generic) 
    deriving FromJSON


newtype ContractCashFlows = ContractCashFlows {
    cfs :: Map String Payoff
    } 
    deriving stock (Show, Generic) 
    deriving FromJSON

type MyApi = "actus" :> ReqBody '[JSON] ModelInput :> Post '[JSON] ContractCashFlows -- POST /books

myApi :: Proxy MyApi
myApi = Proxy

-- 'client' allows you to produce operations to query an API from a client.
actus :: ModelInput -> ClientM ContractCashFlows
actus = client myApi


main :: IO ()
main = do
  manager' <- newManager defaultManagerSettings
  res <- runClientM (actus undefined) (mkClientEnv manager' (BaseUrl Http "localhost" 8081 ""))
  case res of
    Left err -> putStrLn $ "Error: " ++ show err
    Right books -> print books