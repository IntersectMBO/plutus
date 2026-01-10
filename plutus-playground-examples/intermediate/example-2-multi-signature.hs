{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MultiSig where

import           PlutusTx
import           PlutusTx.Prelude
import           Ledger
import           Ledger.Contexts
import           Ledger.Typed.Scripts
import           Prelude (Semigroup(..))

data MultiSigParams = MultiSigParams
  { signerA :: PubKeyHash
  , signerB :: PubKeyHash
  }
PlutusTx.unstableMakeIsData ''MultiSigParams

{-# INLINABLE mkValidator #-}
mkValidator :: MultiSigParams -> () -> ScriptContext -> Bool
mkValidator params _ ctx =
    traceIfFalse "Missing signatures" signaturesOk
  where
    info = scriptContextTxInfo ctx
    sigs = txInfoSignatories info
    signaturesOk =
         signerA params `elem` sigs
      && signerB params `elem` sigs

data MS
instance ValidatorTypes MS where
    type instance DatumType MS = MultiSigParams
    type instance RedeemerType MS = ()

typedValidator :: TypedValidator MS
typedValidator = mkTypedValidator @MS
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = wrapValidator @MultiSigParams @()

validator :: Validator
validator = validatorScript typedValidator
