{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

module HelloWorld where

-- TRIM TO HERE
import qualified Data.Text           as T
import           Playground.Contract
import           Plutus.Contract     hiding (when)
import qualified Prelude

-- | A 'Contract' that logs a message.
hello :: Contract () BlockchainActions T.Text ()
hello = logInfo @Prelude.String "Hello, world"

endpoints :: Contract () BlockchainActions T.Text ()
endpoints = hello

mkSchemaDefinitions ''BlockchainActions

$(mkKnownCurrencies [])
