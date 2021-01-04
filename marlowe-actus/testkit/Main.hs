{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}

module Main where

import Data.Proxy
import Network.HTTP.Client (newManager, defaultManagerSettings)
import Servant.API
import Servant.Client
import GHC.Generics     (Generic)
import Data.Aeson.Types (FromJSON, ToJSON)
import Data.Map
import Test.QuickCheck
import Language.Marlowe.ACTUS.Definitions.ContractTerms
import Language.Marlowe.ACTUS.QCGenerator
import Language.Marlowe.ACTUS.Definitions.BusinessEvents
import Data.Time

data ModelInput = ModelInput {
    ct :: ContractTerms
    , rf :: Map Day RiskFactors
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

type MyApi = "actus" :> ReqBody '[JSON] ModelInput :> Post '[JSON] ContractCashFlows

myApi :: Proxy MyApi
myApi = Proxy

actus :: ModelInput -> ClientM ContractCashFlows
actus = client myApi

main :: IO ()
main = do
  ct <- generate contractTermsGen
  rf <- generate (riskFactorsGen ct)
  let input = ModelInput ct rf
  manager' <- newManager defaultManagerSettings
  res <- runClientM (actus input) (mkClientEnv manager' (BaseUrl Http "localhost" 8081 ""))
  case res of
    Left err -> putStrLn $ "Error: " ++ show err
    Right books -> print books