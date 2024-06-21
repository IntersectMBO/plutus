{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE Strict            #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
-- Following is for tx compilation
{-# LANGUAGE DataKinds         #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:remove-trace #-}
module Cardano.Constitution.Validator.Unsorted
    ( constitutionValidator
    , defaultConstitutionValidator
    , mkConstitutionCode
    , defaultConstitutionCode
    ) where

import Cardano.Constitution.Config
import Cardano.Constitution.Validator.Common as Common
import PlutusCore.Version (plcVersion110)
import PlutusTx as Tx
import PlutusTx.Builtins as B
import PlutusTx.Prelude as Tx

-- | Expects a constitution-configuration, statically *OR* at runtime via Tx.liftCode
constitutionValidator :: ConstitutionConfig -> ConstitutionValidator
constitutionValidator cfg = Common.withChangedParams
                            (all (validateParam cfg))

validateParam :: ConstitutionConfig -> (BuiltinData, BuiltinData) -> Bool
validateParam (ConstitutionConfig cfg) (B.unsafeDataAsI -> actualPid, actualValueData) =
    Common.validateParamValue
      -- If param not found, it will error
      (Common.lookupUnsafe actualPid cfg)
      actualValueData

-- | Statically configure the validator with the `defaultConstitutionConfig`.
defaultConstitutionValidator :: ConstitutionValidator
defaultConstitutionValidator = constitutionValidator defaultConstitutionConfig

{-| Make a constitution code by supplied the config at runtime.

See Note [Manually constructing a Configuration value]
-}
mkConstitutionCode :: ConstitutionConfig -> CompiledCode ConstitutionValidator
mkConstitutionCode cCfg = $$(compile [|| constitutionValidator ||])
                          `unsafeApplyCode` liftCode plcVersion110 cCfg

-- | The code of the constitution statically configured with the `defaultConstitutionConfig`.
defaultConstitutionCode :: CompiledCode ConstitutionValidator
defaultConstitutionCode = $$(compile [|| defaultConstitutionValidator ||])
