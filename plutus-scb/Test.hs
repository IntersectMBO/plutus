{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module Test where

import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy            as BSL
import qualified Data.ByteString.Lazy.Char8      as BS8
import           Control.Monad                                     (void)
import           Data.Bifunctor                                    (first)
import           Language.PlutusTx.Coordination.Contracts.Currency (forgeCurrency, CurrencySchema, SimpleMPS(..))
import           Plutus.SCB.Utils                                  (tshow)
import Language.Plutus.Contract.State (ContractRequest)
import Language.Plutus.Contract.Schema (Event)
import Language.Plutus.Contract.Resumable (Response)
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoint

import qualified Plutus.SCB.ContractCLI as CLI

input :: IO BSL.ByteString
input = BSL.readFile "/home/jann/plutus/test.json"

response :: IO (Either BSL.ByteString BSL.ByteString)
response = do
  arg <- input
  let con = first tshow $ void forgeCurrency
  pure $ CLI.runUpdate con arg

req :: IO (Either String (ContractRequest (Event (CurrencySchema))))
req = JSON.eitherDecode <$> input

resp :: IO (Either String (Event (CurrencySchema)))
resp = JSON.eitherDecode <$> BSL.readFile "/home/jann/plutus/test2.json"

myMPS :: SimpleMPS
myMPS =
  SimpleMPS
    { smTokenName = "asd"
    , smAmount    = 1000
    }

resp2 :: BS8.ByteString
resp2 = JSON.encode  myMPS

myEvent :: Event CurrencySchema
myEvent = Endpoint.event @"create-currency" myMPS

resp3 :: BS8.ByteString
resp3 = JSON.encode myEvent

resp4 :: Either String (Event (CurrencySchema))
resp4 = JSON.eitherDecode resp3
