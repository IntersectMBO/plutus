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
import Test.Tasty.Extras (runTestNested, testNested)

main :: IO ()
main = defaultMain $ testGroup "Size regression tests"
  [ runTestNested ["test", "size", "Golden"]
      [ testNested "Rational"
          [ testNested "Eq"
              [ goldenSize "equal" ratEq
              , goldenSize "not-equal" ratNeq
              ]
          , testNested "Ord"
              [ goldenSize "compare" ratCompare
              , goldenSize "less-than-equal" ratLe
              , goldenSize "greater-than-equal" ratGe
              , goldenSize "less-than" ratLt
              , goldenSize "greater-than" ratGt
              , goldenSize "max" ratMax
              , goldenSize "min" ratMin
              ]
          , testNested "Additive"
              [ goldenSize "plus" ratPlus
              , goldenSize "zero" ratZero
              , goldenSize "minus" ratMinus
              , goldenSize "negate-specialized" ratNegate
              ]
          , testNested "Multiplicative"
              [ goldenSize "times" ratTimes
              , goldenSize "one" ratOne
              , goldenSize "scale" ratScale
              ]
          , testNested "Serialization"
              [ goldenSize "toBuiltinData" ratToBuiltin
              , goldenSize "fromBuiltinData" ratFromBuiltin
              , goldenSize "unsafeFromBuiltinData" ratUnsafeFromBuiltin
              ]
          , testNested "Construction"
              [ goldenSize "unsafeRatio" ratMkUnsafe
              , goldenSize "ratio" ratMkSafe
              , goldenSize "fromInteger" ratFromInteger
              ]
          , testNested "Other"
              [ goldenSize "numerator" ratNumerator
              , goldenSize "denominator" ratDenominator
              , goldenSize "round" ratRound
              , goldenSize "truncate" ratTruncate
              , goldenSize "properFraction" ratProperFraction
              , goldenSize "recip" ratRecip
              , goldenSize "abs-specialized" ratAbs
              ]
          ]
      ]
  , testGroup "Comparison"
      [ fitsUnder "negate" ("specialized", ratNegate) ("general", genNegate)
      , fitsUnder "abs" ("specialized", ratAbs) ("general", genAbs)
      , fitsUnder "scale" ("type class method", ratScale)
          ("equivalent in other primitives", genScale)
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
