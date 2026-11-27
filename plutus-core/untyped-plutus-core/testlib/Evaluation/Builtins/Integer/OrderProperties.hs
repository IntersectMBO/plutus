-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

{-| Property tests for the `lessThanInteger` and `lessThanEqualsInteger` builtins
   and their interaction with the arithmetic functions. -}
module Evaluation.Builtins.Integer.OrderProperties
  ( test_integer_order_properties
  , integer_order_property_names
  , generate_integer_order_properties
  )
where

import Prelude hiding (and, not, or)

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common
import Evaluation.Builtins.Integer.Conformance

import Evaluation.Builtins.Conformance (CheckMode, OutputFormat, PropertyFilter, PropertyId (..))

import Test.Cardano.Base.QuickCheck qualified as BaseQC
import Test.QuickCheck.Random (QCGen)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck

numberOfTests :: Int
numberOfTests = 200

{- Tests for standard properties of order relations.  In most of these we create
   totally random inputs and then create terms checking that the expected
   properties are satisfied.  The inputs are completely random, so in some cases
   we'll be checking vacuous implications (for example, in `add_pairs`, where
   only one quarter of the cases will be checking the property that we really
   want to check).  Instead we could have used `suchThat` to generate inputs
   that always satisified the preconditions and then created terms to check that
   the conclusion holds.  It's arguable which of these is better, but the way
   it's done here exercises the comparison builtins more so perhaps increases
   the probability of detecting unexpected behaviour. -}

lte_reflexive :: BigInteger -> Check
lte_reflexive (biginteger -> a) =
  CheckTrue $ lessThanEqualsInteger a a

lte_antisymmetric :: BigInteger -> BigInteger -> Check
lte_antisymmetric (biginteger -> a) (biginteger -> b) =
  CheckTrue $
    (lessThanEqualsInteger a b `and` lessThanEqualsInteger b a)
      `implies` equalsInteger a b

lte_transitive :: BigInteger -> BigInteger -> BigInteger -> Check
lte_transitive (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  CheckTrue $
    (lessThanEqualsInteger a b `and` lessThanEqualsInteger b c)
      `implies` lessThanEqualsInteger a c

-- This implies that lessThanEqualsInteger is a total order.
trichotomy :: BigInteger -> BigInteger -> Check
trichotomy (biginteger -> a) (biginteger -> b) =
  CheckTrue $
    lessThanInteger a b `xor` equalsInteger a b `xor` lessThanInteger b a

-- This establishes a connection between < and <=, allowing us to limit
-- ourselves to checking properties of <=.
lt_versus_lte :: BigInteger -> BigInteger -> Check
lt_versus_lte (biginteger -> a) (biginteger -> b) =
  CheckTrue $
    lessThanEqualsInteger a b `iff` (lessThanInteger a b `xor` equalsInteger a b)

-- Tests of some relations between the comparison operators and the arithmetic
-- operators.

-- Check that a <= b and c <= d => a+c <= b+d.  In conjunction with the ring
-- properties this implies, for example, that the sum of two positive integers
-- is positive and the sum of two negative integers is negative, and that a <=
-- a+k for positive k.
add_pairs :: BigInteger -> BigInteger -> BigInteger -> BigInteger -> Check
add_pairs (biginteger -> a) (biginteger -> b) (biginteger -> c) (biginteger -> d) =
  CheckTrue $
    (lessThanEqualsInteger a b `and` lessThanEqualsInteger c d)
      `implies` lessThanEqualsInteger (addInteger a c) (addInteger b d)

-- Test that the signs of various types of product are correct.
mul_pos_pos :: NonNegative BigInteger -> NonNegative BigInteger -> Check
mul_pos_pos (NonNegative (biginteger -> a)) (NonNegative (biginteger -> b)) =
  CheckTrue $ lessThanEqualsInteger zero (multiplyInteger a b)

mul_pos_neg :: NonNegative BigInteger -> NonPositive BigInteger -> Check
mul_pos_neg (NonNegative (biginteger -> a)) (NonPositive (biginteger -> b)) =
  CheckTrue $ lessThanEqualsInteger (multiplyInteger a b) zero

mul_neg_pos :: NonPositive BigInteger -> NonNegative BigInteger -> Check
mul_neg_pos (NonPositive (biginteger -> a)) (NonNegative (biginteger -> b)) =
  CheckTrue $ lessThanEqualsInteger (multiplyInteger a b) zero

mul_neg_neg :: NonPositive BigInteger -> NonPositive BigInteger -> Check
mul_neg_neg (NonPositive (biginteger -> a)) (NonPositive (biginteger -> b)) =
  CheckTrue $ lessThanEqualsInteger zero (multiplyInteger a b)

-- | Run the properties without writing files, retaining the usual test count.
test_integer_order_properties :: TestTree
test_integer_order_properties =
  testGroup "Property tests involving integer ordering" $
    testPropertySpecs (BaseQC.withNumTests numberOfTests) integerOrderProperties

-- | Properties shared by the test suite and the conformance test generator.
integerOrderProperties :: [PropertySpec (Gen Check)]
integerOrderProperties =
  [ propertySpec "lte_reflexive" "lessThanEqualsInteger is reflexive" lte_reflexive
  , propertySpec "lte_antisymmetric" "lessThanEqualsInteger is antisymmetric" lte_antisymmetric
  , propertySpec "lte_transitive" "lessThanEqualsInteger is transitive" lte_transitive
  , propertySpec "lt_versus_lte" "a <= b <=> a < b or a = b" lt_versus_lte
  , propertySpec "trichotomy" "a < b or a = b or b < a" trichotomy
  , propertySpec "add_pairs" "a <= b and c <= d => addInteger a c <= addInteger b d" add_pairs
  , propertySpec "mul_pos_pos" "multiplyInteger (>= 0) (>= 0) >= 0" mul_pos_pos
  , propertySpec "mul_pos_neg" "multiplyInteger (>= 0) (<= 0) <= 0" mul_pos_neg
  , propertySpec "mul_neg_pos" "multiplyInteger (<= 0) (>= 0) <= 0" mul_neg_pos
  , propertySpec "mul_neg_neg" "multiplyInteger (<= 0) (<= 0) >= 0" mul_neg_neg
  ]

generate_integer_order_properties
  :: OutputFormat -> CheckMode -> PropertyFilter -> FilePath -> Int -> QCGen -> IO [PropertyReport]
generate_integer_order_properties format mode include outputDir numFiles seed =
  generatePropertySpecs
    format
    mode
    include
    outputDir
    numFiles
    seed
    conformanceSuiteDirectory
    integerOrderProperties

-- | Qualified property names, without sampling inputs or evaluating checks.
integer_order_property_names :: [PropertyId]
integer_order_property_names =
  propertySpecPropertyIds conformanceSuiteDirectory integerOrderProperties

conformanceSuiteDirectory :: [String]
conformanceSuiteDirectory = ["integer", "OrderProperties"]
