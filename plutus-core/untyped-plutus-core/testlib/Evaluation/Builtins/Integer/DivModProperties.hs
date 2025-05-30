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
prop_div_mod_compatible :: Integer -> (NonZero Integer) -> Property
prop_div_mod_compatible (integer -> a) (NonZero (integer -> b)) =
  let t = addInteger (multiplyInteger b (divideInteger a b) ) (modInteger a b)
  in evalOkEq t a

prop_mod_periodic :: Integer -> (NonZero Integer) -> Integer -> Property
prop_mod_periodic (integer -> a) (NonZero (integer -> b)) (integer -> k) =
  let t1 = modInteger a b
      t2 = modInteger (addInteger a (multiplyInteger k b)) b
  in evalOkEq t1 t2

-- For b > 0, 0 <= a `mod` b < b;
prop_modSize_pos :: Integer -> (Positive Integer) -> Property
prop_modSize_pos (integer -> a) (Positive (integer -> b)) =
  let t1 = lessThanEqualsInteger zero (modInteger a b)
      t2 = lessThanInteger (modInteger a b) b
  in evalOkEq t1 true .&&. evalOkEq t2 true

-- For b < 0, b < a `mod` b <= 0
prop_modSize_neg :: Integer -> (Negative Integer) -> Property
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
    testProp "div_0_fails" prop_div_0_fails
  , testProp "mod_0_fails" prop_mod_0_fails
  , testProp "div_mod_compatible" prop_div_mod_compatible
  , testProp "mod_periodic" prop_mod_periodic
  , testProp "modSize_pos" prop_modSize_pos
  , testProp "modSize_neg" prop_modSize_neg
  , testProp "div_pos_pos" prop_div_pos_pos
  , testProp "div_neg_pos" prop_div_neg_pos
  , testProp "div_pos_neg" prop_div_pos_neg
  , testProp "div_neg_neg" prop_div_neg_neg
  , testProp "mod_pos_pos" prop_mod_pos_pos
  , testProp "mod_neg_pos" prop_mod_neg_pos
  , testProp "mod_pos_neg" prop_mod_pos_neg
  , testProp "mod_neg_neg" prop_mod_neg_neg
  ]

