-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

{- | Property tests for the `quotientInteger` and `remainderInteger` builtins -}
module Evaluation.Builtins.Integer.QuotRemProperties (test_integer_quot_rem_properties)
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common as C

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

withNTests :: Testable prop => prop -> Property
withNTests = withMaxSuccess 250

prop_quot_0_fails :: Integer -> Property
prop_quot_0_fails (integer -> a) =
  fails (quotientInteger a zero)

prop_rem_0_fails :: Integer -> Property
prop_rem_0_fails (integer -> a) =
  fails (remainderInteger a zero)

-- b /= 0 => a = b * (a `quot` b) + (a `rem` b)
prop_quot_rem_compatible :: Integer -> (NonZero Integer) -> Property
prop_quot_rem_compatible (integer -> a) (NonZero (integer -> b)) =
  let t = addInteger (multiplyInteger b (quotientInteger a b) ) (remainderInteger a b)
  in evalOkEq t a

prop_rem_periodic :: Integer -> (NonZero Integer) -> Integer -> Property
prop_rem_periodic (integer -> a) (NonZero (integer -> b)) (integer -> k) =
  let t1 = remainderInteger a b
      t2 = remainderInteger (addInteger a (multiplyInteger k b)) b
  in evalOkEq t1 t2

-- For a >= 0 and b > 0, 0 <= |a `rem` b| < |b|
-- The sign of the remainder is a bit tricky in this case.  We test that the
-- absolute value of the remainder is in the expected range and leave the sign
-- to later tests.
prop_rem_size :: Integer -> (NonZero Integer) -> Property
prop_rem_size (integer -> a) (NonZero (integer -> b)) =
  let r = C.abs (remainderInteger a b)
      t1 = lessThanEqualsInteger zero r
      t2 = lessThanInteger r (C.abs b)
  in evalOkEq t1 true .&&. evalOkEq t2 true

ge0 :: PlcTerm -> PlcTerm
ge0 t = lessThanEqualsInteger zero t

le0 :: PlcTerm -> PlcTerm
le0 t = lessThanEqualsInteger t zero

{- Sign tests for quotientInteger. We test that the signs are as follows for
   q = quotientInteger a b:

   a b   q
  ---------
   + +   +
   - +   -
   + -   -
   - -   +
-}

prop_quot_pos_pos :: (NonNegative Integer) -> (Positive Integer) -> Property
prop_quot_pos_pos (NonNegative (integer -> a)) (Positive (integer -> b)) =
  let t = ge0 (quotientInteger a b)
  in evalOkEq t true

prop_quot_neg_pos :: (NonPositive Integer) -> (Positive Integer) -> Property
prop_quot_neg_pos (NonPositive (integer -> a)) (Positive (integer -> b)) =
  let t = le0 (quotientInteger a b)
  in evalOkEq t true

prop_quot_pos_neg :: (NonNegative Integer) -> (Negative Integer) -> Property
prop_quot_pos_neg (NonNegative (integer -> a)) (Negative (integer -> b)) =
  let t = le0 (quotientInteger a b)
  in evalOkEq t true

prop_quot_neg_neg :: (NonPositive Integer) -> (Negative Integer) -> Property
prop_quot_neg_neg (NonPositive (integer -> a)) (Negative (integer -> b)) =
  let t =  ge0 (quotientInteger a b)
  in evalOkEq t true

{- Sign tests for remainderInteger. We test that the signs are as follows for
   r = remainderInteger a b:

   a b   r
  ---------
   + +   +
   - +   -
   + -   +
   - -   -
-}
prop_rem_pos_pos :: (NonNegative Integer) -> (Positive Integer) -> Property
prop_rem_pos_pos (NonNegative (integer -> a)) (Positive (integer -> b)) =
  let t = ge0 (remainderInteger a b)
  in evalOkEq t true

prop_rem_neg_pos :: (NonPositive Integer) -> (Positive Integer) -> Property
prop_rem_neg_pos (NonPositive (integer -> a)) (Positive (integer -> b)) =
  let t = le0 (remainderInteger a b)
  in evalOkEq t true

prop_rem_pos_neg :: (NonNegative Integer) -> (Negative Integer) -> Property
prop_rem_pos_neg (NonNegative (integer -> a)) (Negative (integer -> b)) =
  let t = ge0 (remainderInteger a b)
  in evalOkEq t true

prop_rem_neg_neg :: (NonPositive Integer) -> (Negative Integer) -> Property
prop_rem_neg_neg (NonPositive (integer -> a)) (Negative (integer -> b)) =
  let t = le0 (remainderInteger a b)
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
       -99 mod -44 = -11    -99 rem  -44 = -11
-}

-- a >=0 && b > 0 => a div b >= 0 and a mod b >= 0
-- a <=0 && b > 0 => a div b <= 0 and a mod b >= 0
-- a >=0 && b < 0 => a div b <= 0 and a mod b <= 0
-- a < 0 && b < 0 => a div b >= 0 and a mod b <= 0

-- For b > 0, 0 <= a `mod` b < b;
-- For b < 0, b <  a `mod` b <= 0

prop1 :: Integer -> NonZero Integer -> Integer -> Property
prop1  (integer -> a) (NonZero (integer -> b)) (integer -> k) =
  let t1 = remainderInteger (addInteger (multiplyInteger k b) a) b
      t2 = addInteger (quotientInteger a b) k
  in evalOkEq t1 t2

test_integer_quot_rem_properties :: TestTree
test_integer_quot_rem_properties =
  let testProp s p = testProperty s $ withNTests p
  in
  testGroup "Property tests for quotientInteger and remainderInteger"
  [
    testProp "quotientInteger _ 0 always fails" prop_quot_0_fails
  , testProp "remainderInteger _ 0 always fails" prop_rem_0_fails
  , testProp "quotientInteger and remainderInteger are compatible" prop_quot_rem_compatible
  , testProp "remainderInteger size   " prop_rem_size
  , testProp "quotientInteger + + = +"  prop_quot_pos_pos
  , testProp "quotientInteger - + = -"  prop_quot_neg_pos
  , testProp "quotientInteger + - = -"  prop_quot_pos_neg
  , testProp "quotientInteger - - = +"  prop_quot_neg_neg
  , testProp "remainderInteger + + = +" prop_rem_pos_pos
  , testProp "remainderInteger - + = -" prop_rem_neg_pos
  , testProp "remainderInteger + - = +" prop_rem_pos_neg
  , testProp "remainderInteger - - = -" prop_rem_neg_neg
--  , testProp "prop1" prop1
  ]

{-
Div

 a b   q
---------
 + +   +
 - +   -
 + -   -
 - -   +

Mod

 a b   r
---------
 + +   +
 - +   +
 + -   -
 - -   -


        99 div  44 =   2     99 quot  44 =   2
       -99 div  44 =  -3    -99 quot  44 =  -2
        99 div -44 =  -3     99 quot -44 =  -2
       -99 div -44 =   2    -99 quot -44 =   2

        99 mod  44 =  11     99 rem   44 =  11
       -99 mod  44 =  33    -99 rem   44 = -11
        99 mod -44 = -33     99 rem  -44 =  11
       -99 mod -44 = -11    -99 rem  -44 = -11

-}
