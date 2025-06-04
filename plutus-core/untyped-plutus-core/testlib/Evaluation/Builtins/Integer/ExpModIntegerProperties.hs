-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

{- | Property tests for the `expModInteger` builtin -}
module Evaluation.Builtins.Integer.ExpModIntegerProperties (test_expModInteger_properties)
where

import Evaluation.Builtins.Common

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

numberOfTests :: Int
numberOfTests = 400

testProp :: Testable prop => TestName -> prop -> TestTree
testProp s p = testProperty s $ withMaxSuccess numberOfTests p

expModInteger :: Integer -> Integer -> Integer -> PlcTerm
expModInteger (integer -> a) (integer -> e) (integer -> m) =
  mkIterAppNoAnn (builtin () PLC.ExpModInteger) [a, e ,m]

-- Is a^e defined modulo m?  This depends on the properties of gcd, which we
-- just assume behaves properly.
powerExists :: Integer -> Integer -> Integer -> Bool
powerExists a e m =
  e>=0 || (e < 0 && gcd a m == 1)

-- expModInteger a e m always fails if m<=0
prop_bad_modulus :: Gen Property
prop_bad_modulus = do
  a <- arbitrary
  e <- arbitrary
  m <- arbitrary `suchThat` (<=0)
  let t = expModInteger a e m
  pure $ fails t

-- expModInteger a e 1 = 0 for all b and e
prop_modulus_one :: Gen Property
prop_modulus_one = do
  a <- arbitrary
  e <- arbitrary
  let t = expModInteger a e 1
  pure $ evalOkEq t zero

-- Test that expModInteger a e m always lies between 0 and m-1 (inclusive)
prop_in_range :: Gen Property
prop_in_range = do
  m <- arbitrary `suchThat` (>=1)
  e <- arbitrary
  a <- arbitrary `suchThat` (\a -> powerExists a e m)
  let t = expModInteger a e m
      lb = mkApp2 PLC.LessThanEqualsInteger (integer 0) t
      ub = mkApp2 PLC.LessThanEqualsInteger t (mkApp2 PLC.SubtractInteger (integer m) (integer 1))
  pure $ evalOkTrue lb .&&. evalOkTrue ub

-- For m > 1, a^0 = 1 (equals 1, not congruent to 1)
prop_power_zero :: Gen Property
prop_power_zero = do
  a <- arbitrary
  m <- arbitrary `suchThat` (>1)
  let t = expModInteger a 0 m
  pure $ evalOkEq t one

-- For m >= 1, expModInteger a 1 m = a (mod m) for all a
prop_power_one :: Gen Property
prop_power_one = do
  a <- arbitrary
  m <- arbitrary `suchThat` (>=1)
  let t1 = expModInteger a 1 m
      t2 = mkApp2 PLC.ModInteger (mkConstant () a) (mkConstant () m)
  pure $ evalOkEq t1 t2

-- For m >= 1 and e >= 0, expModInteger a e m exists for all a
prop_positive_exponent :: Gen Property
prop_positive_exponent = do
  e <- arbitrary `suchThat` (>=0)
  m <- arbitrary `suchThat` (>=1)
  a <- arbitrary
  let t = expModInteger a e m
  pure $ ok t

-- If m > 1, e < 0, and gcd a m = 1, expModInteger a e m succeeds
prop_negative_exponent_good :: Gen Property
prop_negative_exponent_good = do
  m <- arbitrary `suchThat` (>1)
  a <- arbitrary `suchThat` (\a -> gcd a m == 1)
  e <- arbitrary `suchThat` (<0)
  let t = expModInteger a e m
  pure $ ok t

-- If m > 1, e < 0, and gcd a m /= 1, expModInteger a e m fails
prop_negative_exponent_bad :: Gen Property
prop_negative_exponent_bad = do
  m <- arbitrary `suchThat` (>1)
  a <- arbitrary `suchThat` (\a -> gcd a m /= 1)
  e <- arbitrary `suchThat` (<0)
  let t = expModInteger a e m
  pure $ fails t

-- If m > 1 and gcd a m = 1, expModInteger a e m succeeds for all e and is the
-- multiplicative inverse of expModInteger a (-e) m modulo m.
prop_negated_exponent_inverse :: Gen Property
prop_negated_exponent_inverse = do
  m <- arbitrary `suchThat` (>1)
  a <- arbitrary `suchThat` (\a -> gcd a m == 1)
  e <- arbitrary -- Positive or negative
  let t1 = expModInteger a e m
      t2 = expModInteger a (-e) m
      t = mkApp2 PLC.ModInteger (mkApp2 PLC.MultiplyInteger t1 t2) (mkConstant () m)
  pure $ evalOkEq t one  -- For m=1 this would be zero.

-- (ab)^e mod m = a^e * b^e mod m
prop_multiplicative :: Gen Property
prop_multiplicative = do
  m <- arbitrary `suchThat` (>1)
  e <- arbitrary
  a <- arbitrary `suchThat` (\a -> powerExists a e m)
  b <- arbitrary `suchThat` (\b -> powerExists b e m)
  let t1 = expModInteger (a*b) e m
      t2 = mkApp2 PLC.ModInteger (mkApp2 PLC.MultiplyInteger (expModInteger a e m) (expModInteger b e m)) (integer m)
  pure $ evalOkEq t1 t2

-- a^(e+e') = a^e*a^e' whenever both powers exist
prop_exponent_additive :: Gen Property
prop_exponent_additive = do
  e <- arbitrary
  f <- arbitrary
  m <- arbitrary `suchThat` (>1)
  a <- arbitrary `suchThat` (\a -> powerExists a e m && powerExists a f m)
  let t1 = expModInteger a (e+f) m
      t2 = mkApp2 PLC.ModInteger (mkApp2 PLC.MultiplyInteger (expModInteger a e m) (expModInteger a f m)) (integer m)
  pure $ evalOkEq t1 t2

-- a^e mod m is the same for all members of a particular congruence class.
prop_periodic :: Gen Property
prop_periodic = do
  m <- arbitrary `suchThat` (>1)
  e <- arbitrary
  k <- arbitrary
  a <- arbitrary `suchThat` (\a -> powerExists a e m)
  let t1 = expModInteger a e m
      t2 = expModInteger (a+k*m) e  m
  pure $ evalOkEq t1 t2

-- Test that a power exists when it should. This overlaps with some of the
-- earlier tests.
prop_power_exists :: Gen Property
prop_power_exists = do
   m <- arbitrary `suchThat` (>1)
   e <- arbitrary
   a <- arbitrary `suchThat` (\a -> powerExists a e m)
   let t = expModInteger a e m
   pure $ ok t

-- Test that a power doesn't exist when it shouldn't. This overlaps with some of
-- the earlier tests.
prop_power_does_not_exist :: Gen Property
prop_power_does_not_exist = do
  m <- arbitrary `suchThat` (>1)
  e <- arbitrary
  a <- arbitrary
  let t = expModInteger a e m
  pure $ not (powerExists a e m) ==> fails t

test_expModInteger_properties :: TestTree
test_expModInteger_properties =
  testGroup "Property tests for expModInteger"
    [ testProp "modulus <= 0 -> error" prop_bad_modulus
    , testProp "a^e mod 1 == 0 for all a and e" prop_modulus_one
    , testProp "Result lies between 0 and m-1" prop_in_range
    , testProp "a^0 mod m == 1" prop_power_zero
    , testProp "a^1 mod m == a mod m" prop_power_one
    , testProp "e >= 0  => a^e mod m exists" prop_positive_exponent
    , testProp "e < 0 && gcd a m == 1 => a^e mod m exists" prop_negative_exponent_good
    , testProp "e < 0 && gcd a m > 1 => a^e mod m does not exist" prop_negative_exponent_bad
    , testProp "e < 0 && gcd a m == 1 => (a^e mod m) * (a^(-e) mod m) = 1 mod m" prop_negated_exponent_inverse
    , testProp "(ab)^e mod m == (a^e * b^e) mod m" prop_multiplicative
    , testProp "a^(e+e') mod m == (a^e * a^e') mod m" prop_exponent_additive
    , testProp "(a+k*m)^e mod m == a^e mod m for all k" prop_periodic
    , testProp "Power exists" prop_power_exists
    , testProp "Power does not exist" prop_power_does_not_exist
    ]
