{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
-- CSE is very unstable and produces different output, likely depending on the version of either
-- @unordered-containers@ or @hashable@.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}

module AsData.Budget.Spec where

import System.FilePath

import Test.Tasty.Extras

import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Test (goldenBudget, goldenEvalCekCatch, goldenPirReadable, goldenUPlcReadable)
import PlutusTx.TH (compile)

import AsData.Budget.Types

tests :: TestNested
tests =
  testNested ("AsData" </> "Budget") . pure $ testNestedGhc
    [ goldenPirReadable "onlyUseFirstField" onlyUseFirstField
    , goldenUPlcReadable "onlyUseFirstField" onlyUseFirstField
    , goldenEvalCekCatch "onlyUseFirstField" [onlyUseFirstField `unsafeApplyCode` inp]
    , goldenBudget "onlyUseFirstField-budget" (onlyUseFirstField `unsafeApplyCode` inp)
    , goldenPirReadable "patternMatching" patternMatching
    , goldenUPlcReadable "patternMatching" patternMatching
    , goldenEvalCekCatch "patternMatching" [patternMatching `unsafeApplyCode` inp]
    , goldenBudget "patternMatching-budget" (patternMatching `unsafeApplyCode` inp)
    , goldenPirReadable "recordFields" recordFields
    , goldenUPlcReadable "recordFields" recordFields
    , goldenEvalCekCatch "recordFields" [recordFields `unsafeApplyCode` inp]
    , goldenBudget "recordFields-budget" (recordFields `unsafeApplyCode` inp)
    , goldenPirReadable "recordFields-manual" recordFieldsManual
    , goldenUPlcReadable "recordFields-manual" recordFieldsManual
    , goldenEvalCekCatch "recordFields-manual" [recordFieldsManual `unsafeApplyCode` inp]
    , goldenBudget "recordFields-budget-manual" (recordFieldsManual `unsafeApplyCode` inp)
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
           in x
                `PlutusTx.addInteger` y
                `PlutusTx.addInteger` z
                `PlutusTx.addInteger` w
                `PlutusTx.addInteger` ( if PlutusTx.lessThanInteger
                                          (y `PlutusTx.addInteger` z)
                                          (x `PlutusTx.addInteger` w)
                                          then x `PlutusTx.addInteger` z
                                          else y `PlutusTx.addInteger` w
                                      )
                `PlutusTx.addInteger` ( if PlutusTx.lessThanInteger
                                          (z `PlutusTx.addInteger` y)
                                          (w `PlutusTx.addInteger` x)
                                          then z `PlutusTx.addInteger` x
                                          else w `PlutusTx.addInteger` y
                                      )
        ||]
    )

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
           in x
                `PlutusTx.addInteger` y
                `PlutusTx.addInteger` z
                `PlutusTx.addInteger` w
                `PlutusTx.addInteger` ( if PlutusTx.lessThanInteger
                                          (y `PlutusTx.addInteger` z)
                                          (x `PlutusTx.addInteger` w)
                                          then x `PlutusTx.addInteger` z
                                          else y `PlutusTx.addInteger` w
                                      )
                `PlutusTx.addInteger` ( if PlutusTx.lessThanInteger
                                          (int3 ints `PlutusTx.addInteger` int2 ints)
                                          (int4 ints `PlutusTx.addInteger` int1 ints)
                                          then
                                            int3 ints
                                              `PlutusTx.addInteger` int1 ints
                                          else
                                            int4 ints
                                              `PlutusTx.addInteger` int2 ints
                                      )
        ||]
    )

-- This is much more efficient than `recordFields` since the manually written
-- field accessors are more CSE-friendly.
recordFieldsManual :: CompiledCode (PlutusTx.BuiltinData -> Integer)
recordFieldsManual =
  $$( compile
        [||
        \d ->
          let ints = PlutusTx.unsafeFromBuiltinData d
              x = int1Manual ints
              y = int2Manual ints
              z = int3Manual ints
              w = int4Manual ints
           in x
                `PlutusTx.addInteger` y
                `PlutusTx.addInteger` z
                `PlutusTx.addInteger` w
                `PlutusTx.addInteger` ( if PlutusTx.lessThanInteger
                                          (y `PlutusTx.addInteger` z)
                                          (x `PlutusTx.addInteger` w)
                                          then x `PlutusTx.addInteger` z
                                          else y `PlutusTx.addInteger` w
                                      )
                `PlutusTx.addInteger` ( if PlutusTx.lessThanInteger
                                          (int3Manual ints `PlutusTx.addInteger` int2Manual ints)
                                          (int4Manual ints `PlutusTx.addInteger` int1Manual ints)
                                          then
                                            int3Manual ints
                                              `PlutusTx.addInteger` int1Manual ints
                                          else
                                            int4Manual ints
                                              `PlutusTx.addInteger` int2Manual ints
                                      )
        ||]
    )

inp :: CompiledCode PlutusTx.BuiltinData
inp = liftCodeDef (PlutusTx.toBuiltinData (Ints 10 20 30 40))
