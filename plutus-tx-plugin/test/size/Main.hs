{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Data.Kind (Type)
import Data.Tagged (Tagged (Tagged))
import PlutusTx.Code (CompiledCode, sizePlc)
import PlutusTx.IsData.Class (fromBuiltinData, toBuiltinData, unsafeFromBuiltinData)
import PlutusTx.Prelude qualified as Plutus
import PlutusTx.Ratio qualified as PlutusRatio
import PlutusTx.TH (compile)
import Prelude
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Providers (IsTest (run, testOptions), singleTest, testFailed, testPassed)
import Type.Reflection (Typeable)

main :: IO ()
main = defaultMain . testGroup "Size regression tests" $ [
  testGroup "Rational" [
    testGroup "Eq" [
      fitsInto "==" ratEq 80,
      fitsInto "/=" ratNeq 90
      ],
    testGroup "Ord" [
      fitsInto "compare" ratCompare 129,
      fitsInto "<=" ratLe 67,
      fitsInto ">=" ratGe 67,
      fitsInto "<" ratLt 67,
      fitsInto ">" ratGt 67,
      fitsInto "max" ratMax 77,
      fitsInto "min" ratMin 77
      ],
    testGroup "Additive" [
      fitsInto "+" ratPlus 186,
      fitsInto "zero" ratZero 20,
      fitsInto "-" ratMinus 186,
      fitsInto "negate (specialized)" ratNegate 32
      ],
    testGroup "Multiplicative" [
      fitsInto "*" ratTimes 178,
      fitsInto "one" ratOne 23,
      fitsInto "scale" ratScale 127
      ],
    testGroup "Serialization" [
      fitsInto "toBuiltinData" ratToBuiltin 87,
      fitsInto "fromBuiltinData" ratFromBuiltin 471,
      fitsInto "unsafeFromBuiltinData" ratUnsafeFromBuiltin 299
      ],
    testGroup "Construction" [
      fitsInto "unsafeRatio" ratMkUnsafe 185,
      fitsInto "ratio" ratMkSafe 292,
      fitsInto "fromInteger" ratFromInteger 21
      ],
    testGroup "Other" [
      fitsInto "numerator" ratNumerator 24,
      fitsInto "denominator" ratDenominator 24,
      fitsInto "round" ratRound 390,
      fitsInto "truncate" ratTruncate 28,
      fitsInto "properFraction" ratProperFraction 61,
      fitsInto "recip" ratRecip 101,
      fitsInto "abs (specialized)" ratAbs 76
      ],
    testGroup "Comparison" [
      fitsUnder "negate" ("specialized", ratNegate) ("general", genNegate),
      fitsUnder "abs" ("specialized", ratAbs) ("general", genAbs),
      fitsUnder "scale" ("type class method", ratScale) ("equivalent in other primitives", genScale)
      ]
    ]
  ]

-- Helpers

-- Size testing for Tasty

fitsInto :: forall (a :: Type) .
  (Typeable a) =>
  String -> CompiledCode a -> Integer -> TestTree
fitsInto name cc = singleTest name . SizeTest cc

data SizeTest (a :: Type) = SizeTest (CompiledCode a) Integer

instance (Typeable a) => IsTest (SizeTest a) where
  run _ (SizeTest cc limit) _ = do
    let estimate = sizePlc cc
    let diff = limit - estimate
    pure $ case signum diff of
      (-1) -> testFailed $ "Exceeded limit by " <> (show . abs $ diff)
      0    -> testPassed $ "AST size: " <> show limit
      _    -> testPassed $ "Remaining budget: " <> show diff
  testOptions = Tagged []

fitsUnder :: forall (a :: Type) .
  (Typeable a) =>
  String -> (String, CompiledCode a) -> (String, CompiledCode a) -> TestTree
fitsUnder name measured = singleTest name . ComparisonTest measured

data ComparisonTest (a :: Type) =
  ComparisonTest (String, CompiledCode a) (String, CompiledCode a)

instance (Typeable a) => IsTest (ComparisonTest a) where
  run _ (ComparisonTest (mName, mCode) (tName, tCode)) _ = do
    let tEstimate = sizePlc tCode
    let mEstimate = sizePlc mCode
    let diff = tEstimate - mEstimate
    pure $ case signum diff of
      (-1) -> testFailed . renderFailed (tName, tEstimate) (mName, mEstimate) $ diff
      0    -> testPassed . renderEstimates (tName, tEstimate) $ (mName, mEstimate)
      _    -> testPassed . renderExcess (tName, tEstimate) (mName, mEstimate) $ diff
  testOptions = Tagged []

renderFailed :: (String, Integer) -> (String, Integer) -> Integer -> String
renderFailed tData mData diff = renderEstimates tData mData <>
                                "Exceeded by: " <> show diff

renderEstimates :: (String, Integer) -> (String, Integer) -> String
renderEstimates (tName, tEstimate) (mName, mEstimate) =
  "Target: " <> tName <> "; size " <> show tEstimate <> "\n" <>
  "Measured: " <> mName <> "; size " <> show mEstimate <> "\n"

renderExcess :: (String, Integer) -> (String, Integer) -> Integer -> String
renderExcess tData mData diff = renderEstimates tData mData <>
                                "Remaining slack: " <> show diff

-- Compiled definitions

ratEq :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Bool)
ratEq = $$(compile [|| (Plutus.==) ||])

ratNeq :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Bool)
ratNeq = $$(compile [|| (Plutus./=) ||])

ratCompare :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Ordering)
ratCompare = $$(compile [|| Plutus.compare ||])

ratLe :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Bool)
ratLe = $$(compile [|| (Plutus.<=) ||])

ratLt :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Bool)
ratLt = $$(compile [|| (Plutus.<) ||])

ratGe :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Bool)
ratGe = $$(compile [|| (Plutus.>=) ||])

ratGt :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Bool)
ratGt = $$(compile [|| (Plutus.>) ||])

ratMax :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Rational)
ratMax = $$(compile [|| Plutus.max ||])

ratMin :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Rational)
ratMin = $$(compile [|| Plutus.min ||])

ratPlus :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Rational)
ratPlus = $$(compile [|| (Plutus.+) ||])

ratZero :: CompiledCode Plutus.Rational
ratZero = $$(compile [|| Plutus.zero ||])

ratMinus :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Rational)
ratMinus = $$(compile [|| (Plutus.-) ||])

ratNegate :: CompiledCode (Plutus.Rational -> Plutus.Rational)
ratNegate = $$(compile [|| PlutusRatio.negate ||])

ratTimes :: CompiledCode (Plutus.Rational -> Plutus.Rational -> Plutus.Rational)
ratTimes = $$(compile [|| (Plutus.*) ||])

ratOne :: CompiledCode Plutus.Rational
ratOne = $$(compile [|| Plutus.one ||])

ratScale :: CompiledCode (Plutus.Integer -> Plutus.Rational -> Plutus.Rational)
ratScale = $$(compile [|| Plutus.scale ||])

ratToBuiltin :: CompiledCode (Plutus.Rational -> Plutus.BuiltinData)
ratToBuiltin = $$(compile [|| toBuiltinData ||])

ratFromBuiltin :: CompiledCode (Plutus.BuiltinData -> Plutus.Maybe Plutus.Rational)
ratFromBuiltin = $$(compile [|| fromBuiltinData ||])

ratUnsafeFromBuiltin :: CompiledCode (Plutus.BuiltinData -> Plutus.Rational)
ratUnsafeFromBuiltin = $$(compile [|| unsafeFromBuiltinData ||])

ratMkUnsafe :: CompiledCode (Plutus.Integer -> Plutus.Integer -> Plutus.Rational)
ratMkUnsafe = $$(compile [|| PlutusRatio.unsafeRatio ||])

ratMkSafe :: CompiledCode (Plutus.Integer -> Plutus.Integer -> Plutus.Maybe Plutus.Rational)
ratMkSafe = $$(compile [|| PlutusRatio.ratio ||])

ratNumerator :: CompiledCode (Plutus.Rational -> Plutus.Integer)
ratNumerator = $$(compile [|| PlutusRatio.numerator ||])

ratDenominator :: CompiledCode (Plutus.Rational -> Plutus.Integer)
ratDenominator = $$(compile [|| PlutusRatio.denominator ||])

ratRound :: CompiledCode (Plutus.Rational -> Plutus.Integer)
ratRound = $$(compile [|| PlutusRatio.round ||])

ratTruncate :: CompiledCode (Plutus.Rational -> Plutus.Integer)
ratTruncate = $$(compile [|| PlutusRatio.truncate ||])

ratProperFraction :: CompiledCode (Plutus.Rational -> (Plutus.Integer, Plutus.Rational))
ratProperFraction = $$(compile [|| PlutusRatio.properFraction ||])

ratRecip :: CompiledCode (Plutus.Rational -> Plutus.Rational)
ratRecip = $$(compile [|| PlutusRatio.recip ||])

ratAbs :: CompiledCode (Plutus.Rational -> Plutus.Rational)
ratAbs = $$(compile [|| PlutusRatio.abs ||])

ratFromInteger :: CompiledCode (Plutus.Integer -> Plutus.Rational)
ratFromInteger = $$(compile [|| PlutusRatio.fromInteger ||])

genNegate :: CompiledCode (Plutus.Rational -> Plutus.Rational)
genNegate = $$(compile [|| Plutus.negate ||])

genAbs :: CompiledCode (Plutus.Rational -> Plutus.Rational)
genAbs = $$(compile [|| Plutus.abs ||])

genScale :: CompiledCode (Plutus.Integer -> Plutus.Rational -> Plutus.Rational)
genScale = $$(compile [|| \s v -> PlutusRatio.fromInteger s Plutus.* v ||])
