{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module AsData.Budget.Spec where

import System.FilePath
import Test.Tasty.Extras

import AsData.Budget.Types
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.TH (compile)
import PlutusTx.Test (goldenBundle)

tests :: TestNested
tests =
  testNested ("AsData" </> "Budget") . pure $
    testNestedGhc
      [ goldenBundle "onlyUseFirstField" onlyUseFirstField (onlyUseFirstField `unsafeApplyCode` inp)
      , goldenBundle
          "onlyUseFirstField-manual"
          onlyUseFirstFieldManual
          (onlyUseFirstFieldManual `unsafeApplyCode` inp)
      , goldenBundle "patternMatching" patternMatching (patternMatching `unsafeApplyCode` inp)
      , goldenBundle "recordFields" recordFields (recordFields `unsafeApplyCode` inp)
      , goldenBundle "destructSum" destructSum (destructSum `unsafeApplyCode` inpSum)
      , goldenBundle
          "destructSum-manual"
          destructSumManual
          (destructSumManual `unsafeApplyCode` inpSumM)
      ]

-- A function that only accesses the first field of `Ints`.
onlyUseFirstField :: CompiledCode (PlutusTx.BuiltinData -> Integer)
onlyUseFirstField =
  $$( compile
        [||
        \d -> case PlutusTx.unsafeFromBuiltinData d of
          Ints {int1 = x} -> x
        ||]
    )

onlyUseFirstFieldManual :: CompiledCode (PlutusTx.BuiltinData -> Integer)
onlyUseFirstFieldManual =
  $$( compile
        [||
        \d -> case PlutusTx.unsafeFromBuiltinData d of
          IntsManual {int1Manual = x} -> x
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

destructSum :: CompiledCode (PlutusTx.BuiltinData -> Ints)
destructSum =
  $$( compile
        [||
        \d ->
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
  $$( compile
        [||
        \d ->
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
