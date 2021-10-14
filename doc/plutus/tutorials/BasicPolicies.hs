{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module BasicPolicies where

import qualified PlutusCore.Default   as PLC
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
oneAtATimePolicy :: () -> ScriptContext -> Bool
oneAtATimePolicy _ ctx =
    -- 'ownCurrencySymbol' lets us get our own hash (= currency symbol)
    -- from the context
    let ownSymbol = ownCurrencySymbol ctx
        txinfo = scriptContextTxInfo ctx
        minted = txInfoMint txinfo
    -- Here we're looking at some specific token name, which we
    -- will assume we've got from elsewhere for now.
    in case Map.lookup ownSymbol (getValue minted) of
        Nothing -> n == 0
        Just tokens -> all
            (\(tname', n') -> if tname' == tname
                then n' == n
                else n' == 0  -- TODO in canonical form there should be no 0 elements in a @Value@, but we don't seem to maintain a canonical form (e.g. see `instance Semigroup Value`)
            )
            (Map.toList tokens)

        -- TODO
        --
        -- This could probably be simplified to:
        --
        --    valueOfCurrency ownSymbol minted == singleton ownSymbol tname 1
        --
        -- with this helper function:
        --
        --    valueOfCurrency :: CurrencySymbol -> Value -> Value
        --    valueOfCurrency currencySymbol
        --      = Map.fromList
        --      . filter (\(k,_) -> k == currencySymbol)
        --      . Map.toList
        --      . getValue

-- We can use 'compile' to turn a minting policy into a compiled Plutus Core program,
-- just as for validator scripts. We also provide a 'wrapMintingPolicy' function
-- to handle the boilerplate.
oneAtATimeCompiled :: CompiledCode (BuiltinData -> BuiltinData -> ())
oneAtATimeCompiled = $$(compile [|| wrapMintingPolicy oneAtATimePolicy ||])
-- BLOCK2
singleSignerPolicy :: ScriptContext -> Bool
singleSignerPolicy ctx = txSignedBy (scriptContextTxInfo ctx) key
-- BLOCK3
