{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
-- Following is for tx compilation
{-# LANGUAGE DataKinds         #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}
module Cardano.Constitution.Validator.Sorted.Static
    ( constitutionValidator
    , constitutionValidatorUntyped
    , defaultConstitutionValidator
    , defaultConstitutionValidatorUntyped
    , defaultConstitutionCode
    ) where

import Cardano.Constitution.Config.Default
import Cardano.Constitution.Config.Predicate
import Cardano.Constitution.Config.Static.TH
import Cardano.Constitution.Config.Types
import Cardano.Constitution.Validator.Common

import PlutusTx as Tx
import PlutusTx.Prelude as Tx
import PlutusTx.SortedMap qualified as SortedMap

-- | The unfoldings of Cardano.Constitution.Config.Static.Default.defaultaConstitutionConfigStatic
-- unexpectedly do not work anymore, so instead of relying on a simple import, we have to
-- redefine the static config here:
defaultConstitutionConfigStatic :: ConstitutionConfigStatic
defaultConstitutionConfigStatic = $(toConfigStatic defaultConstitutionConfig)

-- Expects a constitution-configuration, statically *OR* at runtime via Tx.liftCode
constitutionValidator :: ConstitutionConfigStatic -> ConstitutionValidator
constitutionValidator (ConstitutionConfigStatic cfgSorted) () =
    \case
        -- SORT the ChangedParameters before checking the rules.
        -- Config is expected to be pre-sorted (at compile time).
        GetChangedParamsMap (SortedMap.sort -> cparamsSorted) -> runRules cparamsSorted cfgSorted
        _ -> False

-- The `runRules` is a loop that works element-wise from left-to-right on the 2 sorted maps.
runRules :: SortedMap.SortedMap ParamId PredValue -- ^ the params sorted above at runtime
         -> SortedMap.SortedMap ParamId [PredMeaningApplied] -- ^ the config (sorted by default)
         -> Bool
runRules cparams@(SortedMap.minViewWithKey -> cparamsView) cfg@(SortedMap.minViewWithKey -> cfgView) =
    case cparamsView of
        Nothing ->
            -- NOTE: this script will succeed on an empty cparams;
            -- is it then the responsibility of the cardano-ledger to first sanitize cparams?
            True
        Just ((actualPid,actualValue), cparamsRest) ->
            case cfgView of
                Nothing -> True -- ran out of config, ignore the rest of params and accept proposal
                Just ((expectedPid, predsApplied), cfgRest) ->
                    case actualPid `compare` expectedPid of
                        EQ -> all ($ actualValue) predsApplied
                             && -- drop both heads, and continue checking the next changed param
                             runRules cparamsRest cfgRest
                        GT -> -- skip configHead pointing to a parameter not being proposed
                             runRules cparams cfgRest
                        LT -> -- config does not know anything about this param, or
                             -- it does not contain restriction on this param.
                             -- Ignore param, by dropping cparamHead and continue
                             runRules cparamsRest cfg


constitutionValidatorUntyped :: ConstitutionConfigStatic -> (BuiltinData -> BuiltinData -> ())
constitutionValidatorUntyped = toUntyped . constitutionValidator

-- cannot have mkConstitutionCode, because ConstitutionConfigStatic cannot be lifted at runtime:
-- mkConstitutionCode::ConstitutionConfigStatic -> CompiledCode (BuiltinData -> BuiltinData -> ())

-- | Statically configure the validator with the `defaultConstitutionConfigStatic`.
defaultConstitutionValidator :: ConstitutionValidator
defaultConstitutionValidator = constitutionValidator defaultConstitutionConfigStatic

defaultConstitutionValidatorUntyped :: BuiltinData -> BuiltinData -> ()
defaultConstitutionValidatorUntyped = toUntyped defaultConstitutionValidator

-- | The code of the constitution statically configured with the `defaultConstitutionConfigStatic`.
defaultConstitutionCode :: CompiledCode (BuiltinData -> BuiltinData -> ())
defaultConstitutionCode = $$(compile [|| defaultConstitutionValidatorUntyped ||])
