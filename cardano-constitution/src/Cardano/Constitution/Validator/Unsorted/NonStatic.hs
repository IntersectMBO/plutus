{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
-- Following is for tx compilation
{-# LANGUAGE DataKinds         #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}
module Cardano.Constitution.Validator.Unsorted.NonStatic
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
constitutionValidator cCfg () =
    \case
        -- NOTE: this script will succeed on an empty cparams;
        -- is it then the responsibility of the cardano-ledger to first sanitize cparams?
        GetChangedParamsMap (AssocMap.toList -> cparams) -> all (paramValidates cCfg) cparams
        _ -> False

paramValidates :: ConstitutionConfig -> (ParamId, PredValue) -> Bool
paramValidates (ConstitutionConfig cfg) (pid, actualValue) =
    case SortedMap.lookup pid cfg of
        Just (unParamConfig -> AssocMap.toList -> paramPreds) ->
            all ( \(predName, expectedPredValue) ->
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
        Nothing -> False -- paramid unknown, the constitution fails for this proposal

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
