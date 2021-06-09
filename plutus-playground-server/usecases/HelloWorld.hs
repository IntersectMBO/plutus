{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# options_ghc -fno-warn-unused-imports #-}

module HelloWorld where

-- TRIM TO HERE
import qualified Data.Text           as T
import           Playground.Contract
import           Plutus.Contract     hiding (when)
import           PlutusTx.Prelude
import qualified Prelude             as Haskell

-- | A 'Contract' that logs a message.
hello :: Contract () EmptySchema T.Text ()
hello = logInfo @Haskell.String "Hello, world"

endpoints :: Contract () EmptySchema T.Text ()
endpoints = hello

mkSchemaDefinitions ''EmptySchema

$(mkKnownCurrencies [])
