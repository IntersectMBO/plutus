module BasicApps where

import           Plutus.Contract

-- BLOCK1
-- | A 'Contract' that prints a message
hello :: Contract s ContractError ()
hello = logInfo "Hello, world"
-- BLOCK2

type DemoSchema = Endpoint "name" String

-- BLOCK3

greeting :: Contract DemoSchema ContractError ()
greeting = do
    hello
    n <- endpoint @"name"
    logInfo $ "Hello, " <> n

-- BLOCK4
