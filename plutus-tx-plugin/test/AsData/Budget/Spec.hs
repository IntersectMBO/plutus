{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module AsData.Budget.Spec where

import System.FilePath

import Test.Tasty.Extras

import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Test (goldenBudget, goldenEvalCekCatch, goldenPirReadable)
import PlutusTx.TH (compile)

import AsData.Budget.Types

tests :: TestNested
tests =
  testNestedGhc
    ("AsData" </> "Budget")
    [ goldenPirReadable "onlyUseFirstField" onlyUseFirstField
    , goldenEvalCekCatch "onlyUseFirstField" $ [onlyUseFirstField `unsafeApplyCode` inp]
    , goldenBudget "onlyUseFirstField-budget" (onlyUseFirstField `unsafeApplyCode` inp)
    , goldenPirReadable "patternMatching" patternMatching
    , goldenEvalCekCatch "patternMatching" $ [patternMatching `unsafeApplyCode` inp]
    , goldenBudget "patternMatching-budget" (patternMatching `unsafeApplyCode` inp)
    , goldenPirReadable "recordFields" recordFields
    , goldenEvalCekCatch "recordFields" $ [recordFields `unsafeApplyCode` inp]
    , goldenBudget "recordFields-budget" (recordFields `unsafeApplyCode` inp)
    ]

-- A function that only accesses the first field of `Ints`.
-- TODO: the compiled code currently accesses all fields.
onlyUseFirstField :: CompiledCode (PlutusTx.BuiltinData -> Integer)
onlyUseFirstField =
  $$( compile
        [||
        \d -> let ints = PlutusTx.unsafeFromBuiltinData d in int1 ints
        ||]
    )

patternMatching :: CompiledCode (PlutusTx.BuiltinData -> Integer)
patternMatching =
  $$( compile
        [||
        \d ->
          let (Ints x y z w) = PlutusTx.unsafeFromBuiltinData d
           in x `PlutusTx.addInteger` y `PlutusTx.addInteger` z `PlutusTx.addInteger` w
        ||]
    )

-- TODO: this does the same thing as `patternMatching`, but is much more expensive,
-- since there's no sharing between the code that accesses different fields.
recordFields :: CompiledCode (PlutusTx.BuiltinData -> Integer)
recordFields =
  $$( compile
        [||
        \d ->
          let ints = PlutusTx.unsafeFromBuiltinData d
              x = int1 ints
              y = int2 ints
              z = int3 ints
              w = int4 ints
           in x `PlutusTx.addInteger` y `PlutusTx.addInteger` z `PlutusTx.addInteger` w
        ||]
    )

inp :: CompiledCode PlutusTx.BuiltinData
inp = liftCodeDef (PlutusTx.toBuiltinData (Ints 10 20 30 40))
