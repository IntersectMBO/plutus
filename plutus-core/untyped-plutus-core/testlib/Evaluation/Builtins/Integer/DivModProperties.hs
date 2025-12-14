-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

-- | Property tests for the `divideInteger` and `modInteger` builtins
module Evaluation.Builtins.Integer.DivModProperties (test_integer_div_mod_properties)
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common

import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.QuickCheck

numberOfTests :: Int
numberOfTests = 200

testProp :: Testable prop => TestName -> prop -> TestTree
testProp s p = testProperty s $ withMaxSuccess numberOfTests p

-- `divideInteger _ 0` always fails.
prop_div_0_fails :: BigInteger -> Property
prop_div_0_fails (biginteger -> a) =
  fails $ divideInteger a zero

-- `modInteger _ 0` always fails.
prop_mod_0_fails :: BigInteger -> Property
prop_mod_0_fails (biginteger -> a) =
  fails $ modInteger a zero

-- b /= 0 => a = b * (a `div` b) + (a `mod` b)
-- This is the crucial property relating `divideInteger` and `modInteger`.
prop_div_mod_compatible :: BigInteger -> NonZero BigInteger -> Property
prop_div_mod_compatible (biginteger -> a) (NonZero (biginteger -> b)) =
  let t = addInteger (multiplyInteger b (divideInteger a b)) (modInteger a b)
   in evalOkEq t a

-- (k*b) `div` b = b and (k*b) `mod` b = 0 for all k
prop_div_mod_multiple :: BigInteger -> NonZero BigInteger -> Property
prop_div_mod_multiple (biginteger -> k) (NonZero (biginteger -> b)) =
  let t1 = divideInteger (multiplyInteger k b) b
      t2 = modInteger (multiplyInteger k b) b
   in evalOkEq t1 k .&&. evalOkEq t2 zero

-- For fixed b, `modInteger _ b` is an additive homomorphism:
-- (a+a') `mod` b = ((a `mod` b) + (a' `mod` b)) `mod` b
-- Together with prop_div_mod_multiple this means that `mod _ b` is
-- periodic: (a+k*b) `mod` b = a mod b` for all k.
prop_mod_additive :: BigInteger -> BigInteger -> NonZero BigInteger -> Property
prop_mod_additive (biginteger -> a) (biginteger -> a') (NonZero (biginteger -> b)) =
  let t1 = modInteger (addInteger a a') b
      t2 = modInteger (addInteger (modInteger a b) (modInteger a' b)) b
   in evalOkEq t1 t2

-- For fixed b, `modInteger _ b` is a multiplicative homomorphism:
-- (a*a') `mod` b = ((a `mod` b) * (a' `mod` b)) `mod` b
prop_mod_multiplicative :: BigInteger -> BigInteger -> NonZero BigInteger -> Property
prop_mod_multiplicative (biginteger -> a) (biginteger -> a') (NonZero (biginteger -> b)) =
  let t1 = modInteger (multiplyInteger a a') b
      t2 = modInteger (multiplyInteger (modInteger a b) (modInteger a' b)) b
   in evalOkEq t1 t2

-- For b > 0, 0 <= a `mod` b < b;
prop_mod_size_pos :: BigInteger -> Positive BigInteger -> Property
prop_mod_size_pos (biginteger -> a) (Positive (biginteger -> b)) =
  let t1 = lessThanEqualsInteger zero (modInteger a b)
      t2 = lessThanInteger (modInteger a b) b
   in evalOkTrue t1 .&&. evalOkTrue t2

-- For b < 0, b < a `mod` b <= 0
prop_mod_size_neg :: BigInteger -> Negative BigInteger -> Property
prop_mod_size_neg (biginteger -> a) (Negative (biginteger -> b)) =
  let t1 = lessThanEqualsInteger (modInteger a b) zero
      t2 = lessThanInteger b (modInteger a b)
   in evalOkTrue t1 .&&. evalOkTrue t2

-- a >= 0 && b > 0  =>  a `div` b >= 0  and  a `mod` b >= 0
-- a <= 0 && b > 0  =>  a `div` b <= 0  and  a `mod` b >= 0
-- a >= 0 && b < 0  =>  a `div` b <= 0  and  a `mod` b <= 0
-- a <  0 && b < 0  =>  a `div` b >= 0  and  a `mod` b <= 0

prop_div_pos_pos :: (NonNegative BigInteger) -> (Positive BigInteger) -> Property
prop_div_pos_pos (NonNegative (biginteger -> a)) (Positive (biginteger -> b)) =
  evalOkTrue $ ge0 (divideInteger a b)

prop_div_neg_pos :: (NonPositive BigInteger) -> (Positive BigInteger) -> Property
prop_div_neg_pos (NonPositive (biginteger -> a)) (Positive (biginteger -> b)) =
  evalOkTrue $ le0 (divideInteger a b)

prop_div_pos_neg :: (NonNegative BigInteger) -> (Negative BigInteger) -> Property
prop_div_pos_neg (NonNegative (biginteger -> a)) (Negative (biginteger -> b)) =
  evalOkTrue $ le0 (divideInteger a b)

prop_div_neg_neg :: (NonPositive BigInteger) -> (Negative BigInteger) -> Property
prop_div_neg_neg (NonPositive (biginteger -> a)) (Negative (biginteger -> b)) =
  evalOkTrue $ ge0 (divideInteger a b)

prop_mod_pos_pos :: (NonNegative BigInteger) -> (Positive BigInteger) -> Property
prop_mod_pos_pos (NonNegative (biginteger -> a)) (Positive (biginteger -> b)) =
  evalOkTrue $ ge0 (modInteger a b)

prop_mod_neg_pos :: (NonPositive BigInteger) -> (Positive BigInteger) -> Property
prop_mod_neg_pos (NonPositive (biginteger -> a)) (Positive (biginteger -> b)) =
  evalOkTrue $ ge0 (modInteger a b)

prop_mod_pos_neg :: (NonNegative BigInteger) -> (Negative BigInteger) -> Property
prop_mod_pos_neg (NonNegative (biginteger -> a)) (Negative (biginteger -> b)) =
  evalOkTrue $ le0 (modInteger a b)

prop_mod_neg_neg :: (NonPositive BigInteger) -> (Negative BigInteger) -> Property
prop_mod_neg_neg (NonPositive (biginteger -> a)) (Negative (biginteger -> b)) =
  evalOkTrue $ le0 (modInteger a b)

test_integer_div_mod_properties :: TestTree
test_integer_div_mod_properties =
  testGroup
    "Property tests for divideInteger and modInteger"
    [ testProp "divideInteger _ 0 always fails" prop_div_0_fails
    , testProp "modInteger _ 0 always fails" prop_mod_0_fails
    , testProp "divideInteger and modInteger are compatible" prop_div_mod_compatible
    , testProp "divideInteger and modInteger behave sensibly on multiples of the divisor" prop_div_mod_multiple
    , testProp "mod is an additive homomorphism" prop_mod_additive
    , testProp "mod is a multiplicative homomorphism" prop_mod_multiplicative
    , testProp "modInteger size is correct for positive modulus" prop_mod_size_pos
    , testProp "modInteger size is correct for negative modulus" prop_mod_size_neg
    , testProp "divideInteger (>= 0) (> 0) >= 0" prop_div_pos_pos
    , testProp "divideInteger (<= 0) (> 0) <= 0" prop_div_neg_pos
    , testProp "divideInteger (>= 0) (< 0) <= 0" prop_div_pos_neg
    , testProp "divideInteger (<= 0) (< 0) >= 0" prop_div_neg_neg
    , testProp "modInteger (>= 0) (> 0) >= 0 " prop_mod_pos_pos
    , testProp "modInteger (>= 0) (< 0) >= 0" prop_mod_neg_pos
    , testProp "modInteger (<= 0) (> 0) <= 0" prop_mod_pos_neg
    , testProp "modInteger (<= 0) (< 0) <= 0" prop_mod_neg_neg
    ]
