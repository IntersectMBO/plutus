-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

-- | Property tests for the `quotientInteger` and `remainderInteger` builtins
module Evaluation.Builtins.Integer.QuotRemProperties
  ( test_integer_quot_rem_properties
  , generate_integer_quot_rem_properties
  )
where

import Prelude hiding (abs)

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

-- `quotientInteger _ 0` always fails.
prop_quot_0_fails :: BigInteger -> Check
prop_quot_0_fails (biginteger -> a) =
  CheckFails $ quotientInteger a zero

-- `remainderInteger _ 0` always fails.
prop_rem_0_fails :: BigInteger -> Check
prop_rem_0_fails (biginteger -> a) =
  CheckFails $ remainderInteger a zero

-- b /= 0 => a = b * (a `quot` b) + (a `rem` b)
-- This is the crucial property relating `quotientInteger` and `remainderInteger`.
prop_quot_rem_compatible :: BigInteger -> NonZero BigInteger -> Check
prop_quot_rem_compatible (biginteger -> a) (NonZero (biginteger -> b)) =
  let t = addInteger (multiplyInteger b (quotientInteger a b)) (remainderInteger a b)
   in CheckEq t a

-- (k*b) `quot` b = k and (k*b) `rem` b = 0 for all k
prop_quot_rem_multiple :: BigInteger -> NonZero BigInteger -> Check
prop_quot_rem_multiple (biginteger -> k) (NonZero (biginteger -> b)) =
  let t1 = quotientInteger (multiplyInteger k b) b
      t2 = remainderInteger (multiplyInteger k b) b
   in CheckBoth (CheckEq t1 k) (CheckEq t2 zero)

-- `remainderInteger _ b` is not an additive homomorphism in general (and hence
-- not periodic) because the sign of `remainderInteger a b` is different for
-- positive and negative a.  For example (writing `rem` for short instead of
-- `remainderInteger`) `rem (-1) 5 = -1` and `rem 5 5 = 0` but `rem (-1+5) 5 =
-- 4`.  However, rem (a + a') b = rem ((rem a b) + (rem a' b)) b if a and a'
-- have the same sign, so we test that instead of checking for arbitrary a and
-- a'.

-- For fixed b, `remainderInteger _ b` is an additive homomorphism on non-negative integers
-- (a+a') `rem` b = ((a `rem` b) + (a' `rem` b)) `rem` b
prop_rem_additive_pos
  :: NonNegative BigInteger -> NonNegative BigInteger -> NonZero BigInteger -> Check
prop_rem_additive_pos (NonNegative (biginteger -> a)) (NonNegative (biginteger -> a')) (NonZero (biginteger -> b)) =
  let t1 = remainderInteger (addInteger a a') b
      t2 = remainderInteger (addInteger (remainderInteger a b) (remainderInteger a' b)) b
   in CheckEq t1 t2

-- For fixed b, `remainderInteger _ b` is an additive homomorphism on non-postive integers
-- (a+a') `rem` b = ((a `rem` b) + (a' `rem` b)) `rem` b
prop_rem_additive_neg
  :: NonPositive BigInteger -> NonPositive BigInteger -> NonZero BigInteger -> Check
prop_rem_additive_neg (NonPositive (biginteger -> a)) (NonPositive (biginteger -> a')) (NonZero (biginteger -> b)) =
  let t1 = remainderInteger (addInteger a a') b
      t2 = remainderInteger (addInteger (remainderInteger a b) (remainderInteger a' b)) b
   in CheckEq t1 t2

-- Somewhat unexpectedly, for fixed b, `remainderInteger _ b` is a
-- multiplicative homomorphism: : (a*a') `rem` b = ((a `rem` b) * (a' `rem` b))
-- `rem` b
prop_rem_multiplicative :: BigInteger -> BigInteger -> NonZero BigInteger -> Check
prop_rem_multiplicative (biginteger -> a) (biginteger -> a') (NonZero (biginteger -> b)) =
  let t1 = remainderInteger (multiplyInteger a a') b
      t2 = remainderInteger (multiplyInteger (remainderInteger a b) (remainderInteger a' b)) b
   in CheckEq t1 t2

-- For a >= 0 and b > 0, 0 <= |a `rem` b| < |b|
-- The sign of the remainder is a bit tricky in this case.  We test that the
-- absolute value of the remainder is in the expected range and leave the sign
-- to later tests.
prop_rem_size :: BigInteger -> NonZero BigInteger -> Check
prop_rem_size (biginteger -> a) (NonZero (biginteger -> b)) =
  let r = abs (remainderInteger a b)
      t1 = lessThanEqualsInteger zero r
      t2 = lessThanInteger r (abs b)
   in CheckBoth (CheckTrue t1) (CheckTrue t2)

-- a >= 0 && b > 0  =>  a `quot` b >= 0  and  a `rem` b >= 0
-- a <= 0 && b > 0  =>  a `quot` b <= 0  and  a `rem` b <= 0
-- a >= 0 && b < 0  =>  a `quot` b <= 0  and  a `rem` b >= 0
-- a <= 0 && b < 0  =>  a `quot` b >= 0  and  a `rem` b <= 0

prop_quot_pos_pos :: NonNegative BigInteger -> Positive BigInteger -> Check
prop_quot_pos_pos (NonNegative (biginteger -> a)) (Positive (biginteger -> b)) =
  CheckTrue $ ge0 (quotientInteger a b)

prop_quot_neg_pos :: NonPositive BigInteger -> Positive BigInteger -> Check
prop_quot_neg_pos (NonPositive (biginteger -> a)) (Positive (biginteger -> b)) =
  CheckTrue $ le0 (quotientInteger a b)

prop_quot_pos_neg :: NonNegative BigInteger -> Negative BigInteger -> Check
prop_quot_pos_neg (NonNegative (biginteger -> a)) (Negative (biginteger -> b)) =
  CheckTrue $ le0 (quotientInteger a b)

prop_quot_neg_neg :: NonPositive BigInteger -> Negative BigInteger -> Check
prop_quot_neg_neg (NonPositive (biginteger -> a)) (Negative (biginteger -> b)) =
  CheckTrue $ ge0 (quotientInteger a b)

prop_rem_pos_pos :: (NonNegative BigInteger) -> (Positive BigInteger) -> Check
prop_rem_pos_pos (NonNegative (biginteger -> a)) (Positive (biginteger -> b)) =
  CheckTrue $ ge0 (remainderInteger a b)

prop_rem_neg_pos :: (NonPositive BigInteger) -> (Positive BigInteger) -> Check
prop_rem_neg_pos (NonPositive (biginteger -> a)) (Positive (biginteger -> b)) =
  CheckTrue $ le0 (remainderInteger a b)

prop_rem_pos_neg :: (NonNegative BigInteger) -> (Negative BigInteger) -> Check
prop_rem_pos_neg (NonNegative (biginteger -> a)) (Negative (biginteger -> b)) =
  CheckTrue $ ge0 (remainderInteger a b)

prop_rem_neg_neg :: (NonPositive BigInteger) -> (Negative BigInteger) -> Check
prop_rem_neg_neg (NonPositive (biginteger -> a)) (Negative (biginteger -> b)) =
  CheckTrue $ le0 (remainderInteger a b)

-- | Run the properties without writing files, retaining the usual test count.
test_integer_quot_rem_properties :: TestTree
test_integer_quot_rem_properties =
  testGroup "Property tests for quotientInteger and remainderInteger" $
    integerQuotRemPropertiesWith $ \_ name prop ->
      testProperty name $ BaseQC.withNumTests numberOfTests prop

{-| Generate the requested number of UPLC programs per property, with expected
results and budgets. No property assertions are run. -}
generate_integer_quot_rem_properties :: OutputFormat -> FilePath -> Int -> QCGen -> IO ()
generate_integer_quot_rem_properties format outputDir numFiles seed =
  sequence_ $
    integerQuotRemPropertiesWith
      ( \identifier _ ->
          generatePropertyFiles
            format
            (outputDir </> "integer" </> "QuotRemProperties")
            numFiles
            seed
            identifier
      )

{-| Share stable identifiers, test descriptions and property definitions.
Identifiers follow the function names, with any @prop_@ prefix removed. -}
integerQuotRemPropertiesWith
  :: (forall prop. (Testable prop, GenerateCases prop) => String -> TestName -> prop -> result)
  -> [result]
integerQuotRemPropertiesWith testProp =
  [ testProp "quot_0_fails" "quotientInteger _ 0 always fails" prop_quot_0_fails
  , testProp "rem_0_fails" "remainderInteger _ 0 always fails" prop_rem_0_fails
  , testProp
      "quot_rem_compatible"
      "quotientInteger and remainderInteger are compatible"
      prop_quot_rem_compatible
  , testProp
      "quot_rem_multiple"
      "quotientInteger and remainderInteger behave sensibly on multiples of the divisor"
      prop_quot_rem_multiple
  , testProp
      "rem_additive_pos"
      "remainderInteger _ b is additive on non-negative inputs"
      prop_rem_additive_pos
  , testProp
      "rem_additive_neg"
      "remainderInteger _ b is additive on non-positive inputs"
      prop_rem_additive_neg
  , testProp
      "rem_multiplicative"
      "remainderInteger is a multiplicative homomorphism"
      prop_rem_multiplicative
  , testProp "rem_size" "remainderInteger size correct" prop_rem_size
  , testProp "quot_pos_pos" "quotientInteger (>= 0) (> 0) >= 0" prop_quot_pos_pos
  , testProp "quot_neg_pos" "quotientInteger (<= 0) (> 0) <= 0" prop_quot_neg_pos
  , testProp "quot_pos_neg" "quotientInteger (>= 0) (< 0) <= 0" prop_quot_pos_neg
  , testProp "quot_neg_neg" "quotientInteger (<= 0) (< 0) >= 0" prop_quot_neg_neg
  , testProp "rem_pos_pos" "remainderInteger (>= 0) (> 0) >= 0" prop_rem_pos_pos
  , testProp "rem_neg_pos" "remainderInteger (<= 0) (> 0) <= 0" prop_rem_neg_pos
  , testProp "rem_pos_neg" "remainderInteger (>= 0) (< 0) >= 0" prop_rem_pos_neg
  , testProp "rem_neg_neg" "remainderInteger (<= 0) (< 0) <= 0" prop_rem_neg_neg
  ]
