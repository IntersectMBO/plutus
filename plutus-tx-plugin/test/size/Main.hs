{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import PlutusTx.Code (CompiledCode)
import PlutusTx.IsData.Class (fromBuiltinData, toBuiltinData, unsafeFromBuiltinData)
import PlutusTx.Prelude qualified as Plutus
import PlutusTx.Ratio qualified as PlutusRatio
import PlutusTx.Test
import PlutusTx.TH (compile)
import Prelude
import Test.Tasty (defaultMain, testGroup)

main :: IO ()
main = defaultMain . testGroup "Size regression tests" $ [
  testGroup "Rational" [
    testGroup "Eq" [
      fitsInto "==" ratEq 55,
      fitsInto "/=" ratNeq 63
      ],
    testGroup "Ord" [
      fitsInto "compare" ratCompare 89,
      fitsInto "<=" ratLe 38,
      fitsInto ">=" ratGe 38,
      fitsInto "<" ratLt 38,
      fitsInto ">" ratGt 38,
      fitsInto "max" ratMax 46,
      fitsInto "min" ratMin 46
      ],
    testGroup "Additive" [
      fitsInto "+" ratPlus 134,
      fitsInto "zero" ratZero 7,
      fitsInto "-" ratMinus 134,
      fitsInto "negate (specialized)" ratNegate 20
      ],
    testGroup "Multiplicative" [
      fitsInto "*" ratTimes 126,
      fitsInto "one" ratOne 10,
      fitsInto "scale" ratScale 100
      ],
    testGroup "Serialization" [
      fitsInto "toBuiltinData" ratToBuiltin 38,
      fitsInto "fromBuiltinData" ratFromBuiltin 411,
      fitsInto "unsafeFromBuiltinData" ratUnsafeFromBuiltin 256
      ],
    testGroup "Construction" [
      fitsInto "unsafeRatio" ratMkUnsafe 168,
      fitsInto "ratio" ratMkSafe 264,
      fitsInto "fromInteger" ratFromInteger 8
      ],
    testGroup "Other" [
      fitsInto "numerator" ratNumerator 7,
      fitsInto "denominator" ratDenominator 7,
      fitsInto "round" ratRound 332,
      fitsInto "truncate" ratTruncate 11,
      fitsInto "properFraction" ratProperFraction 36,
      fitsInto "recip" ratRecip 87,
      fitsInto "abs (specialized)" ratAbs 58
      ],
    testGroup "Comparison" [
      fitsUnder "negate" ("specialized", ratNegate) ("general", genNegate),
      fitsUnder "abs" ("specialized", ratAbs) ("general", genAbs),
      fitsUnder "scale" ("type class method", ratScale) ("equivalent in other primitives", genScale)
      ]
    ]
  ]

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
