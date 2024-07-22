{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE Strict            #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
-- Following is for tx compilation
{-# LANGUAGE DataKinds         #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:remove-trace #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module Cardano.Constitution.Validator.Sorted
    ( mkConstitutionValidator
    , mkConstitutionCode
    ) where

import Cardano.Constitution.Config
import Cardano.Constitution.Validator.Common as Common
import PlutusCore.Version (plcVersion110)
import PlutusTx as Tx
import PlutusTx.Builtins as B
import PlutusTx.Prelude as Tx

-- | The `runRules` is a loop that works element-wise from left-to-right on the 2 sorted maps.
runRules :: [Param]  -- ^ the config (sorted by default)
         -> ChangedParams -- ^ the params (came sorted by the ledger)
         -> Bool
runRules ((expectedPid, paramValue) : cfgRest)
         cparams@((B.unsafeDataAsI -> actualPid, actualValueData) : cparamsRest) =
    case actualPid `compare` expectedPid of
        EQ ->
            Common.validateParamValue paramValue actualValueData
            -- drop both heads, and continue checking the next changed param
            && runRules cfgRest cparamsRest

        GT -> -- skip configHead pointing to a parameter not being proposed
            runRules cfgRest cparams
        LT -> -- actualPid not found in json config, the constitution fails
            False
-- if no cparams left: success
-- if cparams left: it means we reached the end of config without validating all cparams
runRules _ cparams = Tx.null cparams

-- | Expects a constitution-configuration, statically *OR* at runtime via Tx.liftCode
mkConstitutionValidator :: ConstitutionConfig -> ConstitutionValidator
mkConstitutionValidator (ConstitutionConfig cfg) =
    Common.withChangedParams (runRules cfg)

{-| Make a constitution code by supplied the config at runtime.

See Note [Manually constructing a Configuration value]
-}
mkConstitutionCode :: ConstitutionConfig -> CompiledCode ConstitutionValidator
mkConstitutionCode cCfg = $$(compile [|| mkConstitutionValidator ||])
                          `unsafeApplyCode` liftCode plcVersion110 cCfg
