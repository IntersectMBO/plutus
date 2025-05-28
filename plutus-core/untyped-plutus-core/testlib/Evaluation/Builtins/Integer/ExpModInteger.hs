-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

{- | Property tests for the `expModInteger` builtin -}
module Evaluation.Builtins.Integer.ExpModInteger (test_expModInteger_properties)
where

import Evaluation.Builtins.Common

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

withNTests :: Testable prop => prop -> Property
withNTests = withMaxSuccess 250

mkExpMod :: Integer -> Integer -> Integer -> PlcTerm
mkExpMod a e m =
    let a' = integer a
        e' = integer e
        m' = integer m
    in mkIterAppNoAnn (builtin () PLC.ExpModInteger) [a',e',m']

-- Is a^e defined modulo m?  This depends on the properties of gcd, which we
-- just assume behaves properly.
powerExists :: Integer -> Integer -> Integer -> Bool
powerExists a e m =
    e>=0 || (e < 0 && gcd a m == 1)

-- expModInteger a e m always fails if m<=0
test_bad_modulus :: TestTree
test_bad_modulus =
    testProperty
    "modulus <= 0 -> error" .
    withNTests $ do
      a <- arbitrary
      e <- arbitrary
      m <- arbitrary `suchThat` (<=0)
      let t = mkExpMod a e m
      pure $ fails t

-- expModInteger a e 1 = 0 for all b and e
test_modulus_one :: TestTree
test_modulus_one =
    testProperty
    "a^e mod 1 == 0 for all a and e" .
    withNTests $ do
      a <- arbitrary
      e <- arbitrary
      let t = mkExpMod a e 1
      pure $ evalOkEq t zero

-- Test that expModInteger a e m always lies between 0 and m-1 (inclusive)
test_in_range :: TestTree
test_in_range =
    testProperty
    "Result lies between 0 and m-1" .
    withNTests $ do
      m <- arbitrary `suchThat` (>=1)
      e <- arbitrary
      a <- arbitrary `suchThat` (\a -> powerExists a e m)
      let t = mkExpMod a e m
          lb = mkApp2 PLC.LessThanEqualsInteger (integer 0) t
          ub = mkApp2 PLC.LessThanEqualsInteger t (mkApp2 PLC.SubtractInteger (integer m) (integer 1))
      pure $ (evalOkEq lb true) .&&. (evalOkEq ub true)

-- For m>1, a^0 = 1 (equals 1, not congruent to 1)
test_power_zero :: TestTree
test_power_zero =
    testProperty
    "a^0 mod m == 1" .
    withNTests $ do
      a <- arbitrary
      m <- arbitrary `suchThat` (>1)
      let t = mkExpMod a 0 m
      pure $ evalOkEq t one

-- For m>=1, expModInteger a 1 m = a (mod m) for all a
test_power_one :: TestTree
test_power_one =
    testProperty
    "a^1 mod m == a mod m" .
    withNTests $ do
      a <- arbitrary
      m <- arbitrary `suchThat` (>=1)
      let t1 = mkExpMod a 1 m
          t2 = mkApp2 PLC.ModInteger (mkConstant () a) (mkConstant () m)
      pure $ evalOkEq t1 t2

-- For m >= 1 and e>=0, expModInteger a e m exists for all a
test_positive_exponent :: TestTree
test_positive_exponent =
    testProperty
    "e >= 0  => a^e mod m exists" .
    withNTests $ do
      e <- arbitrary `suchThat` (>=0)
      m <- arbitrary `suchThat` (>=1)
      a <- arbitrary
      let t = mkExpMod a e m
      pure $ ok t

-- If m>1, e<0, and gcd a m = 1, expModInteger a e m succeeds
test_negative_exponent_good :: TestTree
test_negative_exponent_good =
    testProperty
    "e < 0 && gcd a m == 1 => a^e mod m exists" .
    withNTests $ do
      m <- arbitrary `suchThat` (>1)
      a <- arbitrary `suchThat` (\a -> gcd a m == 1)
      e <- arbitrary `suchThat` (<0)
      let t = mkExpMod a e m
      pure $ ok t

-- If m>1, e<0, and gcd a m /= 1, expModInteger a e m fails
test_negative_exponent_bad :: TestTree
test_negative_exponent_bad =
    testProperty
    "e < 0 && gcd a m > 1 => a^e mod m does not exist" .
    withNTests $ do
      m <- arbitrary `suchThat` (>1)
      a <- arbitrary `suchThat` (\a -> gcd a m /= 1)
      e <- arbitrary `suchThat` (<0)
      let t = mkExpMod a e m
      pure $ fails t

-- If m>1 and gcd a m = 1, expModInteger a e m succeeds for all e and is the
-- multiplicative inverse of expModInteger a (-e) m modulo m.
test_negated_exponent_inverse :: TestTree
test_negated_exponent_inverse =
    testProperty
    "e < 0 && gcd a m == 1 => (a^e mod m) * (a^(-e) mod m) = 1 mod m" .
    withNTests $ do
      m <- arbitrary `suchThat` (>1)
      a <- arbitrary `suchThat` (\a -> gcd a m == 1)
      e <- arbitrary -- Positive or negative
      let t1 = mkExpMod a e m
          t2 = mkExpMod a (-e) m
          t = mkApp2 PLC.ModInteger (mkApp2 PLC.MultiplyInteger t1 t2) (mkConstant () m)
      pure $ evalOkEq t one  -- For m=1 this would zero.

-- (ab)^e mod m = a^e * b^e mod m
test_multiplicative :: TestTree
test_multiplicative =
    testProperty
    "(ab)^e mod m == (a^e * b^e) mod m" .
    withNTests $ do
      m <- arbitrary `suchThat` (>1)
      e <- arbitrary
      a <- arbitrary `suchThat` (\a -> powerExists a e m)
      b <- arbitrary `suchThat` (\b -> powerExists b e m)
      let t1 = mkExpMod (a*b) e m
          t2 = mkApp2 PLC.ModInteger (mkApp2 PLC.MultiplyInteger (mkExpMod a e m) (mkExpMod b e m)) (integer m)
      pure $ evalOkEq t1 t2

-- a^(e+e') = a^e*a^e' whenever both powers exist
test_exponent_additive :: TestTree
test_exponent_additive =
    testProperty
    "a^(e+e') mod m == (a^e * a^e') mod m" .
    withNTests $ do
      e <- arbitrary
      f <- arbitrary
      m <- arbitrary `suchThat` (>1)
      a <- arbitrary `suchThat` (\a -> powerExists a e m && powerExists a f m)
      let t1 = mkExpMod a (e+f) m
          t2 = mkApp2 PLC.ModInteger (mkApp2 PLC.MultiplyInteger (mkExpMod a e m) (mkExpMod a f m)) (integer m)
      pure $ evalOkEq t1 t2

-- a^e mod m is the same for all members of a particular congruence class.
test_periodic :: TestTree
test_periodic =
    testProperty
    "(a+k*m)^e mod m == a^e mod m for all k" .
    withNTests $ do
      m <- arbitrary `suchThat` (>1)
      e <- arbitrary
      k <- arbitrary
      a <- arbitrary `suchThat` (\a -> powerExists a e m)
      let t1 = mkExpMod a e m
          t2 = mkExpMod (a+k*m) e  m
      pure $ evalOkEq t1 t2

-- Test that a power exists when it should. This overlaps with some of the
-- earlier tests.
test_power_exists :: TestTree
test_power_exists =
    testProperty
    "Power exists" .
    withNTests $ do
      m <- arbitrary `suchThat` (>1)
      e <- arbitrary
      a <- arbitrary `suchThat` (\a -> powerExists a e m)
      let t = mkExpMod a e m
      pure $ ok t

-- Test that a power doesn't exist when it shouldn't. This overlaps with some of
-- the earlier tests.
test_power_does_not_exist :: TestTree
test_power_does_not_exist =
    testProperty
    "Power does not exist" .
    withNTests $ do
      m <- arbitrary `suchThat` (>1)
      e <- arbitrary
      a <- arbitrary
      let t = mkExpMod a e m
      pure $ not (powerExists a e m) ==> fails t

test_expModInteger_properties :: TestTree
test_expModInteger_properties =
    testGroup "expModInteger properties"
                  [ test_bad_modulus
                  , test_modulus_one
                  , test_in_range
                  , test_power_zero
                  , test_power_one
                  , test_positive_exponent
                  , test_negative_exponent_good
                  , test_negative_exponent_bad
                  , test_negated_exponent_inverse
                  , test_multiplicative
                  , test_exponent_additive
                  , test_periodic
                  , test_power_exists
                  , test_power_does_not_exist
                  ]
