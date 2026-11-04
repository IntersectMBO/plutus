-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

-- | Property tests for the `expModInteger` builtin
module Evaluation.Builtins.Integer.ExpModIntegerProperties
  ( test_integer_exp_mod_properties
  , generate_integer_exp_mod_properties
  )
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common (arbitraryBigInteger)
import Evaluation.Builtins.Integer.Conformance

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)

import Evaluation.Builtins.Conformance (OutputFormat)

import System.FilePath ((</>))

import Test.Cardano.Base.QuickCheck qualified as BaseQC
import Test.QuickCheck.Random (QCGen)
import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.QuickCheck

numberOfTests :: Int
numberOfTests = 400

expModInteger :: Integer -> Integer -> Integer -> PlcTerm
expModInteger (integer -> a) (integer -> e) (integer -> m) =
  mkIterAppNoAnn (builtin () PLC.ExpModInteger) [a, e, m]

-- Is a^e defined modulo m?  This depends on the properties of gcd, which we
-- just assume behaves properly.
powerExists :: Integer -> Integer -> Integer -> Bool
powerExists a e m =
  e >= 0 || (e < 0 && gcd a m == 1)

-- expModInteger a e m always fails if m<=0
prop_bad_modulus :: Gen Check
prop_bad_modulus = do
  a <- arbitraryBigInteger
  e <- arbitraryBigInteger
  m <- arbitraryBigInteger `suchThat` (<= 0)
  let t = expModInteger a e m
  pure $ CheckFails t

-- expModInteger a e 1 = 0 for all b and e
prop_modulus_one :: Gen Check
prop_modulus_one = do
  a <- arbitraryBigInteger
  e <- arbitraryBigInteger
  let t = expModInteger a e 1
  pure $ CheckEq t zero

-- Test that expModInteger a e m always lies between 0 and m-1 (inclusive)
prop_in_range :: Gen Check
prop_in_range = do
  m <- arbitraryBigInteger `suchThat` (>= 1)
  e <- arbitraryBigInteger
  a <- arbitraryBigInteger `suchThat` (\a -> powerExists a e m)
  let t = expModInteger a e m
      lb = mkApp2 PLC.LessThanEqualsInteger (integer 0) t
      ub = mkApp2 PLC.LessThanEqualsInteger t (mkApp2 PLC.SubtractInteger (integer m) (integer 1))
  pure $ CheckBoth (CheckTrue lb) (CheckTrue ub)

-- For m > 1, a^0 = 1 (equals 1, not congruent to 1)
prop_power_zero :: Gen Check
prop_power_zero = do
  a <- arbitraryBigInteger
  m <- arbitraryBigInteger `suchThat` (> 1)
  let t = expModInteger a 0 m
  pure $ CheckEq t one

-- For m >= 1, expModInteger a 1 m = a (mod m) for all a
prop_power_one :: Gen Check
prop_power_one = do
  a <- arbitraryBigInteger
  m <- arbitraryBigInteger `suchThat` (>= 1)
  let t1 = expModInteger a 1 m
      t2 = mkApp2 PLC.ModInteger (mkConstant () a) (mkConstant () m)
  pure $ CheckEq t1 t2

-- For m >= 1 and e >= 0, expModInteger a e m exists for all a
prop_positive_exponent :: Gen Check
prop_positive_exponent = do
  e <- arbitraryBigInteger `suchThat` (>= 0)
  m <- arbitraryBigInteger `suchThat` (>= 1)
  a <- arbitraryBigInteger
  let t = expModInteger a e m
  pure $ CheckOk t

-- If m > 1, e < 0, and gcd a m = 1, expModInteger a e m succeeds
prop_negative_exponent_good :: Gen Check
prop_negative_exponent_good = do
  m <- arbitraryBigInteger `suchThat` (> 1)
  a <- arbitraryBigInteger `suchThat` (\a -> gcd a m == 1)
  e <- arbitraryBigInteger `suchThat` (< 0)
  let t = expModInteger a e m
  pure $ CheckOk t

-- If m > 1, e < 0, and gcd a m /= 1, expModInteger a e m fails
prop_negative_exponent_bad :: Gen Check
prop_negative_exponent_bad = do
  m <- arbitraryBigInteger `suchThat` (> 1)
  a <- arbitraryBigInteger `suchThat` (\a -> gcd a m /= 1)
  e <- arbitraryBigInteger `suchThat` (< 0)
  let t = expModInteger a e m
  pure $ CheckFails t

-- If m > 1 and gcd a m = 1, expModInteger a e m succeeds for all e and is the
-- multiplicative inverse of expModInteger a (-e) m modulo m.
prop_negated_exponent_inverse :: Gen Check
prop_negated_exponent_inverse = do
  m <- arbitraryBigInteger `suchThat` (> 1)
  a <- arbitraryBigInteger `suchThat` (\a -> gcd a m == 1)
  e <- arbitraryBigInteger -- Positive or negative
  let t1 = expModInteger a e m
      t2 = expModInteger a (-e) m
      t = mkApp2 PLC.ModInteger (mkApp2 PLC.MultiplyInteger t1 t2) (mkConstant () m)
  pure $ CheckEq t one -- For m=1 this would be zero.

-- (ab)^e mod m = a^e * b^e mod m
prop_multiplicative :: Gen Check
prop_multiplicative = do
  m <- arbitraryBigInteger `suchThat` (> 1)
  e <- arbitraryBigInteger
  a <- arbitraryBigInteger `suchThat` (\a -> powerExists a e m)
  b <- arbitraryBigInteger `suchThat` (\b -> powerExists b e m)
  let t1 = expModInteger (a * b) e m
      t2 =
        mkApp2
          PLC.ModInteger
          (mkApp2 PLC.MultiplyInteger (expModInteger a e m) (expModInteger b e m))
          (integer m)
  pure $ CheckEq t1 t2

-- a^(e+e') = a^e*a^e' whenever both powers exist
prop_exponent_additive :: Gen Check
prop_exponent_additive = do
  e <- arbitraryBigInteger
  f <- arbitraryBigInteger
  m <- arbitraryBigInteger `suchThat` (> 1)
  a <- arbitraryBigInteger `suchThat` (\a -> powerExists a e m && powerExists a f m)
  let t1 = expModInteger a (e + f) m
      t2 =
        mkApp2
          PLC.ModInteger
          (mkApp2 PLC.MultiplyInteger (expModInteger a e m) (expModInteger a f m))
          (integer m)
  pure $ CheckEq t1 t2

-- a^e mod m is the same for all members of a particular congruence class.
prop_periodic :: Gen Check
prop_periodic = do
  m <- arbitraryBigInteger `suchThat` (> 1)
  e <- arbitraryBigInteger
  k <- arbitraryBigInteger
  a <- arbitraryBigInteger `suchThat` (\a -> powerExists a e m)
  let t1 = expModInteger a e m
      t2 = expModInteger (a + k * m) e m
  pure $ CheckEq t1 t2

-- Test that a power exists when it should. This overlaps with some of the
-- earlier tests.
prop_power_exists :: Gen Check
prop_power_exists = do
  m <- arbitraryBigInteger `suchThat` (> 1)
  e <- arbitraryBigInteger
  a <- arbitraryBigInteger `suchThat` (\a -> powerExists a e m)
  let t = expModInteger a e m
  pure $ CheckOk t

-- Test that a power doesn't exist when it shouldn't. This overlaps with some of
-- the earlier tests.
prop_power_does_not_exist :: Gen Check
prop_power_does_not_exist = do
  m <- arbitraryBigInteger `suchThat` (> 1)
  e <- arbitraryBigInteger
  a <- arbitraryBigInteger
  let t = expModInteger a e m
  pure $ CheckImplies (not (powerExists a e m)) (CheckFails t)

-- | Run the properties without writing files, retaining the usual test count.
test_integer_exp_mod_properties :: TestTree
test_integer_exp_mod_properties =
  testGroup "Property tests for expModInteger" $
    integerExpModPropertiesWith $ \_ name prop ->
      testProperty name $ BaseQC.withNumTests numberOfTests prop

{-| Generate the requested number of UPLC programs per property, with expected
results and budgets. No property assertions are run. -}
generate_integer_exp_mod_properties :: OutputFormat -> FilePath -> Int -> QCGen -> IO ()
generate_integer_exp_mod_properties format outputDir numFiles seed =
  sequence_ $
    integerExpModPropertiesWith
      ( \identifier _ ->
          generatePropertyFiles
            format
            (outputDir </> "integer" </> "ExpModIntegerProperties")
            numFiles
            seed
            identifier
      )

{-| Share stable identifiers, test descriptions and property definitions.
Identifiers follow the function names, with any @prop_@ prefix removed. -}
integerExpModPropertiesWith
  :: (forall prop. (Testable prop, GenerateCases prop) => String -> TestName -> prop -> result)
  -> [result]
integerExpModPropertiesWith testProp =
  [ testProp "bad_modulus" "modulus <= 0 -> error" prop_bad_modulus
  , testProp "modulus_one" "a^e mod 1 == 0 for all a and e" prop_modulus_one
  , testProp "in_range" "Result lies between 0 and m-1" prop_in_range
  , testProp "power_zero" "a^0 mod m == 1" prop_power_zero
  , testProp "power_one" "a^1 mod m == a mod m" prop_power_one
  , testProp "positive_exponent" "e >= 0  => a^e mod m exists" prop_positive_exponent
  , testProp
      "negative_exponent_good"
      "e < 0 && gcd a m == 1 => a^e mod m exists"
      prop_negative_exponent_good
  , testProp
      "negative_exponent_bad"
      "e < 0 && gcd a m > 1 => a^e mod m does not exist"
      prop_negative_exponent_bad
  , testProp
      "negated_exponent_inverse"
      "e < 0 && gcd a m == 1 => (a^e mod m) * (a^(-e) mod m) = 1 mod m"
      prop_negated_exponent_inverse
  , testProp "multiplicative" "(ab)^e mod m == (a^e * b^e) mod m" prop_multiplicative
  , testProp "exponent_additive" "a^(e+e') mod m == (a^e * a^e') mod m" prop_exponent_additive
  , testProp "periodic" "(a+k*m)^e mod m == a^e mod m for all k" prop_periodic
  , testProp "power_exists" "Power exists" prop_power_exists
  , testProp "power_does_not_exist" "Power does not exist" prop_power_does_not_exist
  ]
