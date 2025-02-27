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
    , goldenPirReadable "destructSum" destructSum
    , goldenUPlcReadable "destructSum" destructSum
    , goldenEvalCekCatch "destructSum" [destructSum `unsafeApplyCode` inpSum]
    , goldenBudget "destructSum-budget" (destructSum `unsafeApplyCode` inpSum)
    , goldenPirReadable "destructSum-manual" destructSumManual
    , goldenUPlcReadable "destructSum-manual" destructSumManual
    , goldenEvalCekCatch "destructSum-manual" [destructSumManual `unsafeApplyCode` inpSumM]
    , goldenBudget "destructSum-budget-manual" (destructSumManual `unsafeApplyCode` inpSumM)
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
        \d -> case PlutusTx.unsafeFromBuiltinData d of
          Ints x y z w ->
            x
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

destructSum :: CompiledCode (PlutusTx.BuiltinData -> Ints)
destructSum =
  $$(compile
      [|| \d ->
          case PlutusTx.unsafeFromBuiltinData d of
            ThisD is -> is
            ThatD is -> is
            TheseD (Ints x1 y1 z1 w1) (Ints x2 y2 z2 w2) ->
              Ints
                (x1 `PlutusTx.addInteger` x2)
                (y1 `PlutusTx.addInteger` y2)
                (z1 `PlutusTx.addInteger` z2)
                (w1 `PlutusTx.addInteger` w2)
      ||]
    )

destructSumManual :: CompiledCode (PlutusTx.BuiltinData -> Ints)
destructSumManual =
  $$(compile
      [|| \d ->
          case PlutusTx.unsafeFromBuiltinData d of
            ThisDManual is -> is
            ThatDManual is -> is
            TheseDManual (Ints x1 y1 z1 w1) (Ints x2 y2 z2 w2) ->
              Ints
                (x1 `PlutusTx.addInteger` x2)
                (y1 `PlutusTx.addInteger` y2)
                (z1 `PlutusTx.addInteger` z2)
                (w1 `PlutusTx.addInteger` w2)
      ||]
    )

inp :: CompiledCode PlutusTx.BuiltinData
inp = liftCodeDef (PlutusTx.toBuiltinData (Ints 10 20 30 40))

inpSum :: CompiledCode PlutusTx.BuiltinData
inpSum = liftCodeDef (PlutusTx.toBuiltinData (TheseD (Ints 10 20 30 40) (Ints 10 20 30 40)))

inpSumM :: CompiledCode PlutusTx.BuiltinData
inpSumM = liftCodeDef (PlutusTx.toBuiltinData (TheseDManual (Ints 10 20 30 40) (Ints 10 20 30 40)))
