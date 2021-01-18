module HelloWorld where

import qualified Data.Text                 as T
import           Language.Plutus.Contract  hiding (when)
import           Language.PlutusTx.Prelude
import           Playground.Contract


-- BLOCK1
-- | A 'Contract' that logs a message.
hello :: Contract BlockchainActions T.Text ()
hello = logInfo @String "Hello, world"
-- BLOCK2


endpoints = hello

mkSchemaDefinitions ''BlockchainActions

$(mkKnownCurrencies [])
