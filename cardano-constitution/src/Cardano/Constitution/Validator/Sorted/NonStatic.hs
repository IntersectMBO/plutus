{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
-- Following is for tx compilation
{-# LANGUAGE DataKinds         #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}
module Cardano.Constitution.Validator.Sorted.NonStatic
    ( constitutionValidator
    , constitutionValidatorUntyped
    , mkConstitutionCode
    , defaultConstitutionValidator
    , defaultConstitutionValidatorUntyped
    , defaultConstitutionCode
    ) where

import Cardano.Constitution.Config.Default
import Cardano.Constitution.Config.Predicate
import Cardano.Constitution.Config.Types
import Cardano.Constitution.Validator.Common

import PlutusCore.Version (plcVersion110)
import PlutusTx as Tx
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Prelude as Tx
import PlutusTx.SortedMap qualified as SortedMap

-- Expects a constitution-configuration, statically *OR* at runtime via Tx.liftCode
constitutionValidator :: ConstitutionConfig -> ConstitutionValidator
constitutionValidator (ConstitutionConfig cfgSorted) () =
    \case
        -- SORT the ChangedParameters before checking the rules.
        -- Config is expected to be pre-sorted (either at compile time or at Tx.liftCode-time).
        GetChangedParamsMap (SortedMap.sort -> cparamsSorted) -> runRules cparamsSorted cfgSorted
        _ -> False

-- The `runRules` is a loop that works element-wise from left-to-right on the 2 sorted maps.
runRules :: SortedMap.SortedMap ParamId PredValue -- ^ the params sorted above at runtime
         -> SortedMap.SortedMap ParamId ParamConfig -- ^ the config (sorted by default)
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
                Just ((expectedPid, unParamConfig -> AssocMap.toList -> paramPreds), cfgRest) ->
                    case actualPid `compare` expectedPid of
                        EQ -> all ( \(predName, expectedPredValue) ->
                                   -- this LOOKUP is the price we pay for the NonStatic version
                                   -- and is missing from the Static version
                                   case AssocMap.lookup predName defaultPredMeanings of
                                       Just predMeaning -> predMeaning expectedPredValue actualValue
                                       -- This cannot happen as long as the defaultPredMeanings
                                       -- is a complete Map (or a total function), which should be.
                                       -- We include this guard to make the pattern-match complete
                                       -- by failing since the constitution clearly has problems.
                                       Nothing          -> False
                             ) paramPreds
                        GT -> -- skip configHead pointing to a parameter not being proposed
                             runRules cparams cfgRest
                        LT -> -- config does not know anything about this param, or
                             -- it does not contain restriction on this param.
                             -- Ignore param, by dropping cparamHead and continue
                             runRules cparamsRest cfg

constitutionValidatorUntyped :: ConstitutionConfig -> (BuiltinData -> BuiltinData -> ())
constitutionValidatorUntyped = toUntyped . constitutionValidator

-- | Make a constitution code by supplied the config at runtime.
mkConstitutionCode :: ConstitutionConfig -> CompiledCode (BuiltinData -> BuiltinData -> ())
mkConstitutionCode cCfg = $$(compile [|| constitutionValidatorUntyped ||])
                          `unsafeApplyCode` liftCode plcVersion110 cCfg

-- | Statically configure the validator with the `defaultConstitutionConfig`.
defaultConstitutionValidator :: ConstitutionValidator
defaultConstitutionValidator = constitutionValidator defaultConstitutionConfig

defaultConstitutionValidatorUntyped :: BuiltinData -> BuiltinData -> ()
defaultConstitutionValidatorUntyped = toUntyped defaultConstitutionValidator

-- | The code of the constitution statically configured with the `defaultConstitutionConfig`.
defaultConstitutionCode :: CompiledCode (BuiltinData -> BuiltinData -> ())
defaultConstitutionCode = $$(compile [|| defaultConstitutionValidatorUntyped ||])
