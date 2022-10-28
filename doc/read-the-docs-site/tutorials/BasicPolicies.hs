-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module BasicPolicies where

import PlutusCore.Default qualified as PLC
import PlutusTx
import PlutusTx.Lift
import PlutusTx.Prelude

import PlutusLedgerApi.V1.Contexts
import PlutusLedgerApi.V1.Crypto
import PlutusLedgerApi.V1.Scripts
import PlutusLedgerApi.V1.Value

tname :: TokenName
tname = error ()

key :: PubKeyHash
key = error ()

-- BLOCK1
oneAtATimePolicy :: () -> ScriptContext -> Bool
oneAtATimePolicy _ ctx =
    -- 'ownCurrencySymbol' lets us get our own hash (= currency symbol)
    -- from the context
    let ownSymbol = ownCurrencySymbol ctx
        txinfo = scriptContextTxInfo ctx
        minted = txInfoMint txinfo
    -- Here we're looking at some specific token name, which we
    -- will assume we've got from elsewhere for now.
    in valueOf minted ownSymbol tname == 1
-- BLOCK2
-- The 'plutus-ledger' package from 'plutus-apps' provides helper functions to automate
-- some of this boilerplate.
oneAtATimePolicyUntyped :: BuiltinData -> BuiltinData -> ()
-- 'check' fails with 'error' if the argument is not 'True'.
oneAtATimePolicyUntyped r c = check $ oneAtATimePolicy (unsafeFromBuiltinData r) (unsafeFromBuiltinData c)

-- We can use 'compile' to turn a minting policy into a compiled Plutus Core program,
-- just as for validator scripts.
oneAtATimeCompiled :: CompiledCode (BuiltinData -> BuiltinData -> ())
oneAtATimeCompiled = $$(compile [|| oneAtATimePolicyUntyped ||])
-- BLOCK3
singleSignerPolicy :: () -> ScriptContext -> Bool
singleSignerPolicy _ ctx = txSignedBy (scriptContextTxInfo ctx) key
-- BLOCK4
