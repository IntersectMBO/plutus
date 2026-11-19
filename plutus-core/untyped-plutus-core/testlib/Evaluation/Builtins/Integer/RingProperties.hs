-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

-- | Property tests for the `addInteger`, `subtractInteger`, and `multiplyInteger` builtins
module Evaluation.Builtins.Integer.RingProperties
  ( test_integer_ring_properties
  , integer_ring_property_names
  , generate_integer_ring_properties
  )
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common
import Evaluation.Builtins.Integer.Conformance

import Evaluation.Builtins.Conformance (OutputFormat, PropertyFilter, PropertyId (..))

import Test.QuickCheck.Random (QCGen)
import Test.Tasty (TestTree, testGroup)
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
    testPropertySpecs id integerRingProperties

-- | Properties shared by the test suite and the corpus generator.
integerRingProperties :: [PropertySpec (Gen Check)]
integerRingProperties =
  [ propertySpec "addition_associative" "addInteger is associative" prop_addition_associative
  , propertySpec "addition_commutative" "addInteger is commutative" prop_addition_commutative
  , propertySpec
      "zero_additive_identity"
      "0 is an identity element for addInteger"
      prop_zero_additive_identity
  , propertySpec
      "add_subtract_inverse"
      "subtraction is the inverse of addition"
      prop_add_subtract_inverse
  , propertySpec
      "multiplication_associative"
      "multiplyInteger is associative"
      prop_multiplication_associative
  , propertySpec
      "multiplication_commutative"
      "multiplyInteger is commutative"
      prop_multiplication_commutative
  , propertySpec
      "one_multiplicative_identity"
      "1 is a multiplicative identity"
      prop_one_multiplicative_identity
  , propertySpec "distibutive" "multiplyInteger distributes over addInteger" prop_distibutive
  ]

generate_integer_ring_properties
  :: OutputFormat -> PropertyFilter -> FilePath -> Int -> QCGen -> IO ()
generate_integer_ring_properties format include outputDir numFiles seed =
  generatePropertySpecs
    format
    include
    outputDir
    numFiles
    seed
    conformanceSuiteDirectory
    integerRingProperties

-- | Qualified property names, without sampling inputs or evaluating checks.
integer_ring_property_names :: [PropertyId]
integer_ring_property_names =
  propertySpecPropertyIds conformanceSuiteDirectory integerRingProperties

conformanceSuiteDirectory :: [String]
conformanceSuiteDirectory = ["integer", "RingProperties"]
