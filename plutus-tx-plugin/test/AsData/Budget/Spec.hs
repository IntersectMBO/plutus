{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}

module AsData.Budget.Spec where

import System.FilePath
import Test.Tasty.Extras

import AsData.Budget.Types
import Plinth.Plugin (plinthc)
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Test

tests :: TestNested
tests =
  testNested ("AsData" </> "Budget") . pure $
    testNestedGhc
      [ goldenBundle "onlyUseFirstField" onlyUseFirstField (onlyUseFirstField `unsafeApplyCode` inp)
      , goldenBundle
          "onlyUseFirstField-manual"
          onlyUseFirstFieldManual
          (onlyUseFirstFieldManual `unsafeApplyCode` inp)
      , goldenBundle "richInts1" richInts1 (richInts1 `unsafeApplyCode` inpRich)
      , goldenBundle "richInts2" richInts2 (richInts2 `unsafeApplyCode` inpRich)
      , goldenBundle "richInts3" richInts3 (richInts3 `unsafeApplyCode` inpRich)
      , goldenBundle "patternMatching" patternMatching (patternMatching `unsafeApplyCode` inp)
      , goldenBundle "recordFields" recordFields (recordFields `unsafeApplyCode` inp)
      , goldenBundle "destructSum" destructSum (destructSum `unsafeApplyCode` inpSum)
      , goldenBundle
          "destructSum-manual"
          destructSumManual
          (destructSumManual `unsafeApplyCode` inpSumM)
      , goldenBundle
          "richSumA"
          richSum
          (richSum `unsafeApplyCode` inpRichSumA)
      , goldenEvalCekCatchBudget
          "richSumB"
          (richSum `unsafeApplyCode` inpRichSumB)
      , goldenEvalCekCatchBudget
          "richSumC"
          (richSum `unsafeApplyCode` inpRichSumC)
      ]

-- A function that only accesses the first field of `Ints`.
onlyUseFirstField :: CompiledCode (PlutusTx.BuiltinData -> Integer)
onlyUseFirstField =
  plinthc
    ( \d -> case PlutusTx.unsafeFromBuiltinData d of
        Ints {int1 = x} -> x
    )

onlyUseFirstFieldManual :: CompiledCode (PlutusTx.BuiltinData -> Integer)
onlyUseFirstFieldManual =
  plinthc
    ( \d -> case PlutusTx.unsafeFromBuiltinData d of
        IntsManual {int1Manual = x} -> x
    )

richInts1 :: CompiledCode (PlutusTx.BuiltinData -> Integer)
richInts1 =
  plinthc
    ( \d -> case PlutusTx.unsafeFromBuiltinData d of
        RichInts {ri16 = x} -> x
    )

richInts2 :: CompiledCode (PlutusTx.BuiltinData -> Integer)
richInts2 =
  plinthc
    ( \d -> case PlutusTx.unsafeFromBuiltinData d of
        RichInts {ri9 = x, ri14 = y} -> PlutusTx.addInteger x y
    )

richInts3 :: CompiledCode (PlutusTx.BuiltinData -> Integer)
richInts3 =
  plinthc
    ( \d -> case PlutusTx.unsafeFromBuiltinData d of
        RichInts {ri4 = x, ri8 = y, ri15 = z} -> PlutusTx.addInteger x (PlutusTx.addInteger y z)
    )

patternMatching :: CompiledCode (PlutusTx.BuiltinData -> Integer)
patternMatching =
  plinthc
    ( \d -> case PlutusTx.unsafeFromBuiltinData d of
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
    )

recordFields :: CompiledCode (PlutusTx.BuiltinData -> Integer)
recordFields =
  plinthc
    ( \d ->
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
    )

destructSum :: CompiledCode (PlutusTx.BuiltinData -> Ints)
destructSum =
  plinthc
    ( \d ->
        matchTheseD
          (PlutusTx.unsafeFromBuiltinData d)
          (\is -> is)
          (\is -> is)
          ( \(Ints x1 y1 z1 w1) (Ints x2 y2 z2 w2) ->
              Ints
                (x1 `PlutusTx.addInteger` x2)
                (y1 `PlutusTx.addInteger` y2)
                (z1 `PlutusTx.addInteger` z2)
                (w1 `PlutusTx.addInteger` w2)
          )
    )

destructSumManual :: CompiledCode (PlutusTx.BuiltinData -> Ints)
destructSumManual =
  plinthc
    ( \d ->
        case PlutusTx.unsafeFromBuiltinData d of
          ThisDManual is -> is
          ThatDManual is -> is
          TheseDManual (Ints x1 y1 z1 w1) (Ints x2 y2 z2 w2) ->
            Ints
              (x1 `PlutusTx.addInteger` x2)
              (y1 `PlutusTx.addInteger` y2)
              (z1 `PlutusTx.addInteger` z2)
              (w1 `PlutusTx.addInteger` w2)
    )

-- Only a small number of fields of a sum type are accessed.
richSum :: CompiledCode (PlutusTx.BuiltinData -> Integer)
richSum =
  plinthc
    ( \d0 ->
        matchRichSum
          (PlutusTx.unsafeFromBuiltinData d0)
          (\_ b _ _ _ _ -> b)
          (\_ _ c _ _ _ g -> PlutusTx.addInteger c g)
          (\_ _ _ d _ _ _ _ i _ _ _ _ n _ _ -> PlutusTx.addInteger d (PlutusTx.addInteger i n))
    )

inp :: CompiledCode PlutusTx.BuiltinData
inp = liftCodeDef (PlutusTx.toBuiltinData (Ints 10 20 30 40))

inpRich :: CompiledCode PlutusTx.BuiltinData
inpRich = liftCodeDef (PlutusTx.toBuiltinData (RichInts 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16))

inpSum :: CompiledCode PlutusTx.BuiltinData
inpSum = liftCodeDef (PlutusTx.toBuiltinData (TheseD (Ints 10 20 30 40) (Ints 10 20 30 40)))

inpSumM :: CompiledCode PlutusTx.BuiltinData
inpSumM = liftCodeDef (PlutusTx.toBuiltinData (TheseDManual (Ints 10 20 30 40) (Ints 10 20 30 40)))

inpRichSumA :: CompiledCode PlutusTx.BuiltinData
inpRichSumA =
  liftCodeDef
    ( PlutusTx.toBuiltinData
        (RichA 10 20 30 40 50 60)
    )

inpRichSumB :: CompiledCode PlutusTx.BuiltinData
inpRichSumB =
  liftCodeDef
    ( PlutusTx.toBuiltinData
        (RichB 10 20 30 40 50 60 70)
    )

inpRichSumC :: CompiledCode PlutusTx.BuiltinData
inpRichSumC =
  liftCodeDef
    ( PlutusTx.toBuiltinData
        (RichC 10 20 30 40 50 60 70 80 90 100 110 120 130 140 150 160)
    )
