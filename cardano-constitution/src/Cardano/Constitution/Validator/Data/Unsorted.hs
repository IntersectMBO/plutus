-- Following is for tx compilation
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:remove-trace #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:target-version=1.1.0 #-}

module Cardano.Constitution.Validator.Data.Unsorted
  ( constitutionValidator
  , defaultConstitutionValidator
  , mkConstitutionCode
  , defaultConstitutionCode
  ) where

import Cardano.Constitution.Config
import Cardano.Constitution.Validator.Data.Common as Common
import PlutusCore.Version (plcVersion110)
import PlutusTx as Tx
import PlutusTx.BuiltinList qualified as BuiltinList
import PlutusTx.Builtins as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Prelude as Tx

-- | Expects a constitution-configuration, statically *OR* at runtime via Tx.liftCode
constitutionValidator :: ConstitutionConfig -> ConstitutionValidator
constitutionValidator cfg =
  Common.withChangedParams
    (BuiltinList.all (validateParam cfg))

validateParam :: ConstitutionConfig -> BI.BuiltinPair BuiltinData BuiltinData -> Bool
validateParam (ConstitutionConfig cfg) cparam =
  BI.casePair cparam $ \actualPidData actualValueData ->
    Common.validateParamValue
      -- If param not found, it will error
      (lookupUnsafe (B.unsafeDataAsI actualPidData) cfg)
      actualValueData

-- | An unsafe version of PlutusTx.AssocMap.lookup, specialised to Integer keys
lookupUnsafe :: Integer -> [(Integer, v)] -> v
lookupUnsafe k = go
  where
    go [] = traceError "Unsorted lookup failed"
    go ((k', i) : xs') =
      if k `B.equalsInteger` k'
        then i
        else go xs'
{-# INLINEABLE lookupUnsafe #-}

-- | Statically configure the validator with the `defaultConstitutionConfig`.
defaultConstitutionValidator :: ConstitutionValidator
defaultConstitutionValidator = constitutionValidator defaultConstitutionConfig

{-| Make a constitution code by supplied the config at runtime.

See Note [Manually constructing a Configuration value] -}
mkConstitutionCode :: ConstitutionConfig -> CompiledCode ConstitutionValidator
mkConstitutionCode cCfg =
  $$(compile [||constitutionValidator||])
    `unsafeApplyCode` liftCode plcVersion110 cCfg

-- | The code of the constitution statically configured with the `defaultConstitutionConfig`.
defaultConstitutionCode :: CompiledCode ConstitutionValidator
defaultConstitutionCode = $$(compile [||defaultConstitutionValidator||])
