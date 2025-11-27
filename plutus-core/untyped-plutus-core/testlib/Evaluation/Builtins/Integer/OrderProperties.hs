-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

{-| Property tests for the `lessThanInteger` and `lessThanEqualsInteger` builtins
   and their interaction with the arithmetic functions. -}
module Evaluation.Builtins.Integer.OrderProperties (test_integer_order_properties)
where

import Prelude hiding (and, not, or)

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common

import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.QuickCheck

numberOfTests :: Int
numberOfTests = 200

testProp :: Testable prop => TestName -> prop -> TestTree
testProp s p = testProperty s $ withMaxSuccess numberOfTests p

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

lte_reflexive :: BigInteger -> Property
lte_reflexive (biginteger -> a) =
  evalOkTrue $ lessThanEqualsInteger a a

lte_antisymmetric :: BigInteger -> BigInteger -> Property
lte_antisymmetric (biginteger -> a) (biginteger -> b) =
  evalOkTrue $
    (lessThanEqualsInteger a b `and` lessThanEqualsInteger b a)
      `implies` equalsInteger a b

lte_transitive :: BigInteger -> BigInteger -> BigInteger -> Property
lte_transitive (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  evalOkTrue $
    (lessThanEqualsInteger a b `and` lessThanEqualsInteger b c)
      `implies` lessThanEqualsInteger a c

-- This implies that lessThanEqualsInteger is a total order.
trichotomy :: BigInteger -> BigInteger -> Property
trichotomy (biginteger -> a) (biginteger -> b) =
  evalOkTrue $
    lessThanInteger a b `xor` equalsInteger a b `xor` lessThanInteger b a

-- This establishes a connection between < and <=, allowing us to limit
-- ourselves to checking properties of <=.
lt_versus_lte :: BigInteger -> BigInteger -> Property
lt_versus_lte (biginteger -> a) (biginteger -> b) =
  evalOkTrue $
    lessThanEqualsInteger a b `iff` (lessThanInteger a b `xor` equalsInteger a b)

-- Tests of some relations between the comparison operators and the arithmetic
-- operators.

-- Check that a <= b and c <= d => a+c <= b+d.  In conjunction with the ring
-- properties this implies, for example, that the sum of two positive integers
-- is positive and the sum of two negative integers is negative, and that a <=
-- a+k for positive k.
add_pairs :: BigInteger -> BigInteger -> BigInteger -> BigInteger -> Property
add_pairs (biginteger -> a) (biginteger -> b) (biginteger -> c) (biginteger -> d) =
  evalOkTrue $
    (lessThanEqualsInteger a b `and` lessThanEqualsInteger c d)
      `implies` lessThanEqualsInteger (addInteger a c) (addInteger b d)

-- Test that the signs of various types of product are correct.
mul_pos_pos :: NonNegative BigInteger -> NonNegative BigInteger -> Property
mul_pos_pos (NonNegative (biginteger -> a)) (NonNegative (biginteger -> b)) =
  evalOkTrue $ lessThanEqualsInteger zero (multiplyInteger a b)

mul_pos_neg :: NonNegative BigInteger -> NonPositive BigInteger -> Property
mul_pos_neg (NonNegative (biginteger -> a)) (NonPositive (biginteger -> b)) =
  evalOkTrue $ lessThanEqualsInteger (multiplyInteger a b) zero

mul_neg_pos :: NonPositive BigInteger -> NonNegative BigInteger -> Property
mul_neg_pos (NonPositive (biginteger -> a)) (NonNegative (biginteger -> b)) =
  evalOkTrue $ lessThanEqualsInteger (multiplyInteger a b) zero

mul_neg_neg :: NonPositive BigInteger -> NonPositive BigInteger -> Property
mul_neg_neg (NonPositive (biginteger -> a)) (NonPositive (biginteger -> b)) =
  evalOkTrue $ lessThanEqualsInteger zero (multiplyInteger a b)

test_integer_order_properties :: TestTree
test_integer_order_properties =
  testGroup
    "Property tests involving integer ordering"
    [ testProp "lessThanEqualsInteger is reflexive" lte_reflexive
    , testProp "lessThanEqualsInteger is antisymmetric" lte_antisymmetric
    , testProp "lessThanEqualsInteger is transitive" lte_transitive
    , testProp "a <= b <=> a < b or a = b" lt_versus_lte
    , testProp "a < b or a = b or b < a" trichotomy
    , testProp "a <= b and c <= d => addInteger a c <= addInteger b d" add_pairs
    , testProp "multiplyInteger (>= 0) (>= 0) >= 0" mul_pos_pos
    , testProp "multiplyInteger (>= 0) (<= 0) <= 0" mul_pos_neg
    , testProp "multiplyInteger (<= 0) (>= 0) <= 0" mul_neg_pos
    , testProp "multiplyInteger (<= 0) (<= 0) >= 0" mul_neg_neg
    ]
