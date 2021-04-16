{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module BasicPolicies where

import qualified PlutusCore.Builtins  as PLC
import qualified PlutusCore.Universe  as PLC
import           PlutusTx
import           PlutusTx.Lift
import           PlutusTx.Prelude

import           Ledger
import           Ledger.Ada
import           Ledger.Typed.Scripts
import           Ledger.Value

tname :: TokenName
tname = error ()

key :: PubKeyHash
key = error ()

-- BLOCK1
oneAtATimePolicy :: ScriptContext -> Bool
oneAtATimePolicy ctx =
    -- 'ownCurrencySymbol' lets us get our own hash (= currency symbol)
    -- from the context
    let ownSymbol = ownCurrencySymbol ctx
        txinfo = scriptContextTxInfo ctx
        forged = txInfoForge txinfo
    -- Here we're looking at some specific token name, which we
    -- will assume we've got from elsewhere for now.
    in valueOf forged ownSymbol tname == 1

-- We can use 'compile' to turn a forging policy into a compiled Plutus Core program,
-- just as for validator scripts. We also provide a 'wrapMonetaryPolicy' function
-- to handle the boilerplate.
oneAtATimeCompiled :: CompiledCode (Data -> ())
oneAtATimeCompiled = $$(compile [|| wrapMonetaryPolicy oneAtATimePolicy ||])
-- BLOCK2
singleSignerPolicy :: ScriptContext -> Bool
singleSignerPolicy ctx = txSignedBy (scriptContextTxInfo ctx) key
-- BLOCK3
