{-# LANGUAGE NoImplicitPrelude #-}

module LinearVesting.TestOptimized where

import LinearVesting.Test (testScriptContext)
import LinearVesting.ValidatorOptimized (validatorOptimizedCode)
import PlutusTx
import PlutusTx.Prelude

validatorOptimizedCodeFullyApplied :: CompiledCode BuiltinUnit
validatorOptimizedCodeFullyApplied =
  validatorOptimizedCode `unsafeApplyCode` liftCodeDef (toBuiltinData testScriptContext)
