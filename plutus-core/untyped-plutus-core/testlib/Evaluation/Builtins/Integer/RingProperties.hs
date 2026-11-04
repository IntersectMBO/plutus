-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

-- | Property tests for the `addInteger`, `subtractInteger`, and `multiplyInteger` builtins
module Evaluation.Builtins.Integer.RingProperties
  ( test_integer_ring_properties
  , generate_integer_ring_properties
  )
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common
import Evaluation.Builtins.Integer.Conformance

import Evaluation.Builtins.Conformance (OutputFormat)

import System.FilePath ((</>))

import Test.QuickCheck.Random (QCGen)
import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.QuickCheck

-- a+(b+c) = (a+b)+c
prop_addition_associative :: BigInteger -> BigInteger -> BigInteger -> Check
prop_addition_associative (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  let t1 = addInteger a (addInteger b c)
      t2 = addInteger (addInteger a b) c
   in CheckEq t1 t2

-- a+b = b+a
prop_addition_commutative :: BigInteger -> BigInteger -> Check
prop_addition_commutative (biginteger -> a) (biginteger -> b) =
  CheckEq (addInteger a b) (addInteger b a)

-- a+0 = a
prop_zero_additive_identity :: BigInteger -> Check
prop_zero_additive_identity (biginteger -> a) =
  CheckEq (addInteger a zero) a

-- (a+b)-b = a
prop_add_subtract_inverse :: BigInteger -> BigInteger -> Check
prop_add_subtract_inverse (biginteger -> a) (biginteger -> b) =
  CheckEq (subtractInteger (addInteger a b) b) a

-- a*(b*c) = (a*b)*c
prop_multiplication_associative
  :: BigInteger -> BigInteger -> BigInteger -> Check
prop_multiplication_associative (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  let t1 = multiplyInteger a (multiplyInteger b c)
      t2 = multiplyInteger (multiplyInteger a b) c
   in CheckEq t1 t2

-- a*b = b*a
prop_multiplication_commutative :: BigInteger -> BigInteger -> Check
prop_multiplication_commutative (biginteger -> a) (biginteger -> b) =
  let t1 = multiplyInteger a b
      t2 = multiplyInteger b a
   in CheckEq t1 t2

-- a*1 = a
prop_one_multiplicative_identity :: BigInteger -> Check
prop_one_multiplicative_identity (biginteger -> a) =
  let t = multiplyInteger a one
   in CheckEq t a

-- a*(b+c) = a*b + a*c
prop_distibutive :: BigInteger -> BigInteger -> BigInteger -> Check
prop_distibutive (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  let t1 = multiplyInteger a (addInteger b c)
      t2 = addInteger (multiplyInteger a b) (multiplyInteger a c)
   in CheckEq t1 t2

-- | Run the properties without writing files, retaining the usual test count.
test_integer_ring_properties :: TestTree
test_integer_ring_properties =
  testGroup "Ring properties for integer arithmetic builtins" $
    integerRingPropertiesWith $
      \_ name prop -> testProperty name prop

{-| Generate the requested number of UPLC programs per property, with expected
results and budgets. No property assertions are run. -}
generate_integer_ring_properties :: OutputFormat -> FilePath -> Int -> QCGen -> IO ()
generate_integer_ring_properties format outputDir numFiles seed =
  sequence_ $
    integerRingPropertiesWith
      ( \identifier _ ->
          generatePropertyFiles format (outputDir </> "integer" </> "RingProperties") numFiles seed identifier
      )

{-| Share stable identifiers, test descriptions and property definitions.
Identifiers follow the function names, with any @prop_@ prefix removed. -}
integerRingPropertiesWith
  :: (forall prop. (Testable prop, GenerateCases prop) => String -> TestName -> prop -> result)
  -> [result]
integerRingPropertiesWith testProp =
  [ testProp "addition_associative" "addInteger is associative" prop_addition_associative
  , testProp "addition_commutative" "addInteger is commutative" prop_addition_commutative
  , testProp
      "zero_additive_identity"
      "0 is an identity element for addInteger"
      prop_zero_additive_identity
  , testProp "add_subtract_inverse" "subtraction is the inverse of addition" prop_add_subtract_inverse
  , testProp
      "multiplication_associative"
      "multiplyInteger is associative"
      prop_multiplication_associative
  , testProp
      "multiplication_commutative"
      "multiplyInteger is commutative"
      prop_multiplication_commutative
  , testProp
      "one_multiplicative_identity"
      "1 is a multiplicative identity"
      prop_one_multiplicative_identity
  , testProp "distibutive" "multiplyInteger distributes over addInteger" prop_distibutive
  ]
