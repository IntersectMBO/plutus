{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
-- Following is for tx compilation
{-# LANGUAGE DataKinds         #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}
module Cardano.Constitution.Validator.Unsorted.Static
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
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Prelude as Tx hiding (toList)
import PlutusTx.SortedMap qualified as SortedMap

-- | The unfoldings of Cardano.Constitution.Config.Static.Default.defaultaConstitutionConfigStatic
-- unexpectedly do not work anymore, so instead of relying on a simple import, we have to
-- redefine the static config here:
defaultConstitutionConfigStatic :: ConstitutionConfigStatic
defaultConstitutionConfigStatic = $(toConfigStatic defaultConstitutionConfig)

-- Expects a constitution-configuration, statically *OR* at runtime via Tx.liftCode
constitutionValidator :: ConstitutionConfigStatic -> ConstitutionValidator
constitutionValidator cCfg () =
    \case
        -- NOTE: this script will succeed on an empty cparams;
        -- is it then the responsibility of the cardano-ledger to first sanitize cparams?
        GetChangedParamsMap (AssocMap.toList -> cparams) -> all (paramValidates cCfg) cparams
        _ -> False

paramValidates :: ConstitutionConfigStatic -> (ParamId,PredValue) -> Bool
paramValidates (ConstitutionConfigStatic cfg) (pid,actualValue) =
    case SortedMap.lookup pid cfg of
        Just predsApplied -> all ($ actualValue) predsApplied
        Nothing -> True -- paramid unknown, the constitution ignores its value and continues

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
