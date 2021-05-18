{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeOperators      #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}

module Main where

import           Control.Monad.Web                                 (maxInterpretationTime)
import           Data.Aeson.Types                                  (FromJSON, ToJSON)
import           Data.Bits                                         (toIntegralSized)
import           Data.Map
import           Data.Proxy
import           Data.Time
import           Data.Time.Units                                   (toMicroseconds)
import           GHC.Generics                                      (Generic)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents
import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Language.Marlowe.ACTUS.QCGenerator
import           Network.HTTP.Client                               (defaultManagerSettings, managerResponseTimeout,
                                                                    newManager, responseTimeoutMicro)
import           Servant.API
import           Servant.Client
import           Test.QuickCheck

data ModelInput = ModelInput {
    ct   :: ContractTerms
    , rf :: Map Day RiskFactors
    }
    deriving stock (Show, Generic)
    deriving ToJSON


data Payoff = Payoff {
    event    :: String
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
  manager' <- newManager $ defaultManagerSettings
    { managerResponseTimeout = maybe
      (managerResponseTimeout defaultManagerSettings)
      responseTimeoutMicro . toIntegralSized
      $ toMicroseconds maxInterpretationTime }
  res <- runClientM (actus input) (mkClientEnv manager' (BaseUrl Http "localhost" 8081 ""))
  case res of
    Left err     -> putStrLn $ "Error: " ++ show err
    Right result -> print result
