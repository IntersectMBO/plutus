-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

-- | Property tests for the `divideInteger` and `modInteger` builtins
module Evaluation.Builtins.Integer.DivModProperties
  ( test_integer_div_mod_properties
  , generate_integer_div_mod_properties
  )
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common
import Evaluation.Builtins.Integer.Conformance

import Evaluation.Builtins.Conformance (OutputFormat)

import System.FilePath ((</>))

import Test.Cardano.Base.QuickCheck qualified as BaseQC
import Test.QuickCheck.Random (QCGen)
import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.QuickCheck

numberOfTests :: Int
numberOfTests = 200

-- `divideInteger _ 0` always fails.
prop_div_0_fails :: BigInteger -> Check
prop_div_0_fails (biginteger -> a) =
  CheckFails $ divideInteger a zero

-- `modInteger _ 0` always fails.
prop_mod_0_fails :: BigInteger -> Check
prop_mod_0_fails (biginteger -> a) =
  CheckFails $ modInteger a zero

-- b /= 0 => a = b * (a `div` b) + (a `mod` b)
-- This is the crucial property relating `divideInteger` and `modInteger`.
prop_div_mod_compatible :: BigInteger -> NonZero BigInteger -> Check
prop_div_mod_compatible (biginteger -> a) (NonZero (biginteger -> b)) =
  let t = addInteger (multiplyInteger b (divideInteger a b)) (modInteger a b)
   in CheckEq t a

-- (k*b) `div` b = k and (k*b) `mod` b = 0 for all k
prop_div_mod_multiple :: BigInteger -> NonZero BigInteger -> Check
prop_div_mod_multiple (biginteger -> k) (NonZero (biginteger -> b)) =
  let t1 = divideInteger (multiplyInteger k b) b
      t2 = modInteger (multiplyInteger k b) b
   in CheckBoth (CheckEq t1 k) (CheckEq t2 zero)

-- For fixed b, `modInteger _ b` is an additive homomorphism:
-- (a+a') `mod` b = ((a `mod` b) + (a' `mod` b)) `mod` b
-- Together with prop_div_mod_multiple this means that `mod _ b` is
-- periodic: (a+k*b) `mod` b = a mod b` for all k.
prop_mod_additive :: BigInteger -> BigInteger -> NonZero BigInteger -> Check
prop_mod_additive (biginteger -> a) (biginteger -> a') (NonZero (biginteger -> b)) =
  let t1 = modInteger (addInteger a a') b
      t2 = modInteger (addInteger (modInteger a b) (modInteger a' b)) b
   in CheckEq t1 t2

-- For fixed b, `modInteger _ b` is a multiplicative homomorphism:
-- (a*a') `mod` b = ((a `mod` b) * (a' `mod` b)) `mod` b
prop_mod_multiplicative :: BigInteger -> BigInteger -> NonZero BigInteger -> Check
prop_mod_multiplicative (biginteger -> a) (biginteger -> a') (NonZero (biginteger -> b)) =
  let t1 = modInteger (multiplyInteger a a') b
      t2 = modInteger (multiplyInteger (modInteger a b) (modInteger a' b)) b
   in CheckEq t1 t2

-- For b > 0, 0 <= a `mod` b < b;
prop_mod_size_pos :: BigInteger -> Positive BigInteger -> Check
prop_mod_size_pos (biginteger -> a) (Positive (biginteger -> b)) =
  let t1 = lessThanEqualsInteger zero (modInteger a b)
      t2 = lessThanInteger (modInteger a b) b
   in CheckBoth (CheckTrue t1) (CheckTrue t2)

-- For b < 0, b < a `mod` b <= 0
prop_mod_size_neg :: BigInteger -> Negative BigInteger -> Check
prop_mod_size_neg (biginteger -> a) (Negative (biginteger -> b)) =
  let t1 = lessThanEqualsInteger (modInteger a b) zero
      t2 = lessThanInteger b (modInteger a b)
   in CheckBoth (CheckTrue t1) (CheckTrue t2)

-- a >= 0 && b > 0  =>  a `div` b >= 0  and  a `mod` b >= 0
-- a <= 0 && b > 0  =>  a `div` b <= 0  and  a `mod` b >= 0
-- a >= 0 && b < 0  =>  a `div` b <= 0  and  a `mod` b <= 0
-- a <  0 && b < 0  =>  a `div` b >= 0  and  a `mod` b <= 0

prop_div_pos_pos :: (NonNegative BigInteger) -> (Positive BigInteger) -> Check
prop_div_pos_pos (NonNegative (biginteger -> a)) (Positive (biginteger -> b)) =
  CheckTrue $ ge0 (divideInteger a b)

prop_div_neg_pos :: (NonPositive BigInteger) -> (Positive BigInteger) -> Check
prop_div_neg_pos (NonPositive (biginteger -> a)) (Positive (biginteger -> b)) =
  CheckTrue $ le0 (divideInteger a b)

prop_div_pos_neg :: (NonNegative BigInteger) -> (Negative BigInteger) -> Check
prop_div_pos_neg (NonNegative (biginteger -> a)) (Negative (biginteger -> b)) =
  CheckTrue $ le0 (divideInteger a b)

prop_div_neg_neg :: (NonPositive BigInteger) -> (Negative BigInteger) -> Check
prop_div_neg_neg (NonPositive (biginteger -> a)) (Negative (biginteger -> b)) =
  CheckTrue $ ge0 (divideInteger a b)

prop_mod_pos_pos :: (NonNegative BigInteger) -> (Positive BigInteger) -> Check
prop_mod_pos_pos (NonNegative (biginteger -> a)) (Positive (biginteger -> b)) =
  CheckTrue $ ge0 (modInteger a b)

prop_mod_neg_pos :: (NonPositive BigInteger) -> (Positive BigInteger) -> Check
prop_mod_neg_pos (NonPositive (biginteger -> a)) (Positive (biginteger -> b)) =
  CheckTrue $ ge0 (modInteger a b)

prop_mod_pos_neg :: (NonNegative BigInteger) -> (Negative BigInteger) -> Check
prop_mod_pos_neg (NonNegative (biginteger -> a)) (Negative (biginteger -> b)) =
  CheckTrue $ le0 (modInteger a b)

prop_mod_neg_neg :: (NonPositive BigInteger) -> (Negative BigInteger) -> Check
prop_mod_neg_neg (NonPositive (biginteger -> a)) (Negative (biginteger -> b)) =
  CheckTrue $ le0 (modInteger a b)

-- | Run the properties without writing files, retaining the usual test count.
test_integer_div_mod_properties :: TestTree
test_integer_div_mod_properties =
  testGroup "Property tests for divideInteger and modInteger" $
    integerDivModPropertiesWith $ \_ name prop ->
      testProperty name $ BaseQC.withNumTests numberOfTests prop

{-| Generate the requested number of UPLC programs per property, with expected
results and budgets. No property assertions are run. -}
generate_integer_div_mod_properties :: OutputFormat -> FilePath -> Int -> QCGen -> IO ()
generate_integer_div_mod_properties format outputDir numFiles seed =
  sequence_ $
    integerDivModPropertiesWith
      ( \identifier _ ->
          generatePropertyFiles
            format
            (outputDir </> "integer" </> "DivModProperties")
            numFiles
            seed
            identifier
      )

{-| Share stable identifiers, test descriptions and property definitions.
Identifiers follow the function names, with any @prop_@ prefix removed. -}
integerDivModPropertiesWith
  :: (forall prop. (Testable prop, GenerateCases prop) => String -> TestName -> prop -> result)
  -> [result]
integerDivModPropertiesWith testProp =
  [ testProp "div_0_fails" "divideInteger _ 0 always fails" prop_div_0_fails
  , testProp "mod_0_fails" "modInteger _ 0 always fails" prop_mod_0_fails
  , testProp "div_mod_compatible" "divideInteger and modInteger are compatible" prop_div_mod_compatible
  , testProp
      "div_mod_multiple"
      "divideInteger and modInteger behave sensibly on multiples of the divisor"
      prop_div_mod_multiple
  , testProp "mod_additive" "mod is an additive homomorphism" prop_mod_additive
  , testProp "mod_multiplicative" "mod is a multiplicative homomorphism" prop_mod_multiplicative
  , testProp "mod_size_pos" "modInteger size is correct for positive modulus" prop_mod_size_pos
  , testProp "mod_size_neg" "modInteger size is correct for negative modulus" prop_mod_size_neg
  , testProp "div_pos_pos" "divideInteger (>= 0) (> 0) >= 0" prop_div_pos_pos
  , testProp "div_neg_pos" "divideInteger (<= 0) (> 0) <= 0" prop_div_neg_pos
  , testProp "div_pos_neg" "divideInteger (>= 0) (< 0) <= 0" prop_div_pos_neg
  , testProp "div_neg_neg" "divideInteger (<= 0) (< 0) >= 0" prop_div_neg_neg
  , testProp "mod_pos_pos" "modInteger (>= 0) (> 0) >= 0 " prop_mod_pos_pos
  , testProp "mod_neg_pos" "modInteger (>= 0) (< 0) >= 0" prop_mod_neg_pos
  , testProp "mod_pos_neg" "modInteger (<= 0) (> 0) <= 0" prop_mod_pos_neg
  , testProp "mod_neg_neg" "modInteger (<= 0) (< 0) <= 0" prop_mod_neg_neg
  ]
