module HelloWorld where

-- TRIM TO HERE
import qualified Data.Text                 as T
import           Language.Plutus.Contract  hiding (when)
import           Language.PlutusTx.Prelude
import           Playground.Contract

-- | A 'Contract' that logs a message.
hello :: Contract BlockchainActions T.Text ()
hello = logInfo @String "Hello, world"

endpoints = hello

mkSchemaDefinitions ''BlockchainActions

$(mkKnownCurrencies [])
