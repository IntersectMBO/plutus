-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

{- | Property tests for the `divideInteger` and `modInteger` builtins -}
module Evaluation.Builtins.Integer.DivModProperties (test_integer_div_mod_properties)
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

withNTests :: Testable prop => prop -> Property
withNTests = withMaxSuccess 250

prop_div_0_fails :: Integer -> Property
prop_div_0_fails (integer -> a) =
  fails (divideInteger a zero)

prop_mod_0_fails :: Integer -> Property
prop_mod_0_fails (integer -> a) =
  fails (modInteger a zero)

-- b /= 0 => a = b * (a `div` b) + (a `mod` b)
prop_div_mod_compatible :: Integer -> NonZero Integer -> Property
prop_div_mod_compatible (integer -> a) (NonZero (integer -> b)) =
  let t = addInteger (multiplyInteger b (divideInteger a b) ) (modInteger a b)
  in evalOkEq t a

-- (k*b) `div` b = b and (k*b) `mod` b = 0 for all k
prop_div_mod_multiple :: Integer -> NonZero Integer -> Property
prop_div_mod_multiple (integer -> k) (NonZero (integer -> b)) =
    let t1 = divideInteger (multiplyInteger k b) b
        t2 = modInteger (multiplyInteger k b) b
    in evalOkEq t1 k .&&. evalOkEq t2 zero

-- For fixed b, `modInteger _ b` is an additive homomorphism:
-- (a+a') `mod` b = ((a `mod` b) + (a' `mod` b)) `mod` b
-- Together with prop_div_mod_multiple this means that `mod _ b` is
-- periodic: (a+k*b) `mod` b = a mod b` for all k.
prop_mod_additive :: Integer -> Integer -> NonZero Integer -> Property
prop_mod_additive (integer -> a) (integer -> a') (NonZero (integer -> b)) =
  let t1 = modInteger (addInteger a a') b
      t2 = modInteger (addInteger (modInteger a b) (modInteger a' b)) b
  in evalOkEq t1 t2

-- For fixed b, `modInteger _ b` is a multiplicative homomorphism:
-- (a*a') `mod` b = ((a `mod` b) * (a' `mod` b)) `mod` b
prop_mod_multiplicative :: Integer -> Integer -> NonZero Integer -> Property
prop_mod_multiplicative (integer -> a) (integer -> a') (NonZero (integer -> b)) =
  let t1 = modInteger (multiplyInteger a a') b
      t2 = modInteger (multiplyInteger (modInteger a b) (modInteger a' b)) b
  in evalOkEq t1 t2

-- For b > 0, 0 <= a `mod` b < b;
prop_modSize_pos :: Integer -> Positive Integer -> Property
prop_modSize_pos (integer -> a) (Positive (integer -> b)) =
  let t1 = lessThanEqualsInteger zero (modInteger a b)
      t2 = lessThanInteger (modInteger a b) b
  in evalOkEq t1 true .&&. evalOkEq t2 true

-- For b < 0, b < a `mod` b <= 0
prop_modSize_neg :: Integer -> Negative Integer -> Property
prop_modSize_neg (integer -> a) (Negative (integer -> b)) =
  let t1 = lessThanEqualsInteger (modInteger a b) zero
      t2 = lessThanInteger b (modInteger a b)
  in evalOkEq t1 true .&&. evalOkEq t2 true

-- a >=0 && b > 0 => a div b >= 0 and a mod b >= 0
-- a <=0 && b > 0 => a div b <= 0 and a mod b >= 0
-- a >=0 && b < 0 => a div b <= 0 and a mod b <= 0
-- a < 0 && b < 0 => a div b >= 0 and a mod b <= 0
ge0 :: PlcTerm -> PlcTerm
ge0 t = lessThanEqualsInteger zero t

le0 :: PlcTerm -> PlcTerm
le0 t = lessThanEqualsInteger t zero

prop_div_pos_pos :: (NonNegative Integer) -> (Positive Integer) -> Property
prop_div_pos_pos (NonNegative (integer -> a)) (Positive (integer -> b)) =
  let t = ge0 (divideInteger a b)
  in evalOkEq t true

prop_div_neg_pos :: (NonPositive Integer) -> (Positive Integer) -> Property
prop_div_neg_pos (NonPositive (integer -> a)) (Positive (integer -> b)) =
  let t = le0 (divideInteger a b)
  in evalOkEq t true

prop_div_pos_neg :: (NonNegative Integer) -> (Negative Integer) -> Property
prop_div_pos_neg (NonNegative (integer -> a)) (Negative (integer -> b)) =
  let t = le0 (divideInteger a b)
  in evalOkEq t true

prop_div_neg_neg :: (NonPositive Integer) -> (Negative Integer) -> Property
prop_div_neg_neg (NonPositive (integer -> a)) (Negative (integer -> b)) =
  let t =  ge0 (divideInteger a b)
  in evalOkEq t true

prop_mod_pos_pos :: (NonNegative Integer) -> (Positive Integer) -> Property
prop_mod_pos_pos (NonNegative (integer -> a)) (Positive (integer -> b)) =
  let t = ge0 (modInteger a b)
  in evalOkEq t true

prop_mod_neg_pos :: (NonPositive Integer) -> (Positive Integer) -> Property
prop_mod_neg_pos (NonPositive (integer -> a)) (Positive (integer -> b)) =
  let t = ge0 (modInteger a b)
  in evalOkEq t true

prop_mod_pos_neg :: (NonNegative Integer) -> (Negative Integer) -> Property
prop_mod_pos_neg (NonNegative (integer -> a)) (Negative (integer -> b)) =
  let t = le0 (modInteger a b)
  in evalOkEq t true

prop_mod_neg_neg :: (NonPositive Integer) -> (Negative Integer) -> Property
prop_mod_neg_neg (NonPositive (integer -> a)) (Negative (integer -> b)) =
  let t = le0 (modInteger a b)
  in evalOkEq t true

{- Sign tests.
   0 <= a `mod` b < b
   (a+kb) `mod` b = a `mod` b
-}

{-
        99 div  44 =   2     99 quot  44 =   2
       -99 div  44 =  -3    -99 quot  44 =  -2
        99 div -44 =  -3     99 quot -44 =  -2
       -99 div -44 =   2    -99 quot -44 =   2

        88 div  44 =   2     88 quot  44 =   2
       -88 div  44 =  -2    -88 quot  44 =  -2
        88 div -44 =  -2     88 quot -44 =  -2
       -88 div -44 =   2    -88 quot -44 =   2

        99 mod  44 =  11     99 rem   44 =  11
       -99 mod  44 =  33    -99 rem   44 = -11
        99 mod -44 = -33     99 rem  -44 =  11
       -99 mod -44 = -11    -99 rem - 44 = -11
-}

-- a >=0 && b > 0 => a div b >= 0 and a mod b >= 0
-- a <=0 && b > 0 => a div b <= 0 and a mod b >= 0
-- a >=0 && b < 0 => a div b <= 0 and a mod b <= 0
-- a < 0 && b < 0 => a div b >= 0 and a mod b <= 0

-- For b > 0, 0 <= a `mod` b < b;
-- For b < 0, b <  a `mod` b <= 0

test_integer_div_mod_properties :: TestTree
test_integer_div_mod_properties =
  let testProp s p = testProperty s $ withNTests p
  in
  testGroup "Property tests for divideInteger and modInteger"
  [
    testProp "divideInteger _ 0 always fails" prop_div_0_fails
  , testProp "modInteger _ 0 always fails" prop_mod_0_fails
  , testProp "divideInteger and modInteger are caompatible" prop_div_mod_compatible
  , testProp "divideInteger and modInteger behave sensibly on multiples of the divisor" prop_div_mod_multiple
  , testProp "mod is an additive homomorphism" prop_mod_additive
  , testProp "mod is a multiplicative homomorphism" prop_mod_multiplicative
  , testProp "modInteger size is correct for positive modulus" prop_modSize_pos
  , testProp "modInteger size is correct for negative modulus" prop_modSize_neg
  , testProp "divideInteger (>= 0) (> 0) >= 0" prop_div_pos_pos
  , testProp "divideInteger (<= 0) (> 0) <= 0" prop_div_neg_pos
  , testProp "divideInteger (>= 0) (< 0) <= 0" prop_div_pos_neg
  , testProp "divideInteger (<= 0) (< 0) >= 0" prop_div_neg_neg
  , testProp "modInteger (>= 0) (> 0) >= 0 " prop_mod_pos_pos
  , testProp "modInteger (>= 0) (< 0) >= 0" prop_mod_neg_pos
  , testProp "modInteger (<= 0) (> 0) <= 0" prop_mod_pos_neg
  , testProp "modInteger (<= 0) (< 0) <= 0" prop_mod_neg_neg
  ]

