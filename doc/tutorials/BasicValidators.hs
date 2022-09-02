-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ViewPatterns        #-}
module BasicValidators where

import PlutusCore.Default qualified as PLC
import PlutusTx
import PlutusTx.Lift
import PlutusTx.Prelude

import PlutusLedgerApi.Common
import PlutusLedgerApi.V1.Contexts
import PlutusLedgerApi.V1.Crypto
import PlutusLedgerApi.V1.Scripts
import PlutusLedgerApi.V1.Value

import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL

import Codec.Serialise
import Flat qualified

import Prelude (IO, print, show)
import Prelude qualified as Haskell

myKeyHash :: PubKeyHash
myKeyHash = Haskell.undefined

-- BLOCK1
-- | A specific date.
newtype Date = Date Integer
-- | Either a specific end date, or "never".
data EndDate = Fixed Integer | Never

-- 'unstableMakeIsData' is a TemplateHaskell function that takes a type name and
-- generates an 'IsData' instance definition for it. It should work for most
-- types, including newtypes and sum types. For production usage use 'makeIsDataIndexed'
-- which ensures that the output is stable across time.
unstableMakeIsData ''Date
unstableMakeIsData ''EndDate
-- BLOCK2
alwaysSucceeds :: BuiltinData -> BuiltinData -> BuiltinData -> ()
alwaysSucceeds _ _ _ = ()

alwaysFails :: BuiltinData -> BuiltinData -> BuiltinData -> ()
alwaysFails _ _ _ = error ()

-- We can use 'compile' to turn a validator function into a compiled Plutus Core program.
-- Here's a reminder of how to do it.
alwaysSucceedsCompiled :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
alwaysSucceedsCompiled = $$(compile [|| alwaysSucceeds ||])
-- BLOCK3
-- | Checks if a date is before the given end date.
beforeEnd :: Date -> EndDate -> Bool
beforeEnd (Date d) (Fixed e) = d <= e
beforeEnd (Date _) Never     = True

-- | Check that the date in the redeemer is before the limit in the datum.
validateDate :: BuiltinData -> BuiltinData -> BuiltinData -> ()
-- The 'check' function takes a 'Bool' and fails if it is false.
-- This is handy since it's more natural to talk about booleans.
validateDate datum redeemer _ = check $ beforeEnd (unsafeFromBuiltinData datum) (unsafeFromBuiltinData redeemer)

dateValidator :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
dateValidator = $$(compile [|| validateDate ||])
-- BLOCK4
validatePayment :: BuiltinData -> BuiltinData -> BuiltinData -> ()
validatePayment _ _ ctx =
    let valCtx = unsafeFromBuiltinData ctx
    -- The 'TxInfo' in the validation context is the representation of the
    -- transaction being validated
        txinfo = scriptContextTxInfo valCtx
    -- 'pubKeyOutputsAt' collects the 'Value' at all outputs which pay to
    -- the given public key hash
        values = pubKeyOutputsAt myKeyHash txinfo
    -- 'fold' sums up all the values, we assert that there must be more
    -- than 1 Ada (more stuff is fine!)
    in check $ valueOf (fold values) adaSymbol adaToken >= 1
--- BLOCK5
-- We can serialize a 'Validator' directly to CBOR
serialisedDateValidator :: SerialisedScript
serialisedDateValidator = serialiseCompiledCode dateValidator

-- The serialized forms can be written or read using normal Haskell IO functionality.
showSerialised :: IO ()
showSerialised = print serialisedDateValidator
-- BLOCK6
-- We can serialize 'CompiledCode' also
serialisedCompiledCode :: BS.ByteString
serialisedCompiledCode = Flat.flat alwaysSucceedsCompiled

-- The 'loadFromFile' function is a drop-in replacement for 'compile', but
-- takes the file path instead of the code to compile.
validatorCodeFromFile :: CompiledCode (() -> () -> ScriptContext -> Bool)
validatorCodeFromFile = $$(loadFromFile "howtos/myscript.uplc")
-- BLOCK7
