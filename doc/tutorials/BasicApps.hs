module BasicApps where

import           Plutus.Contract

type DemoSchema = Endpoint "name" String

-- BLOCK3

greeting :: Contract DemoSchema ContractError ()
greeting = do
    n <- endpoint @"name"
    logInfo $ "Hello, " <> n

-- BLOCK4
