-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

{- | Property tests for the `lessThanInteger` and `lessThanEqualsInteger` builtins
   and their interaction with the arithmetic functions. -}
module Evaluation.Builtins.Integer.OrderProperties (test_integer_order_properties)
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common as C

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

import Prelude hiding (and, not, or)

numberOfTests :: Int
numberOfTests = 200

testProp :: Testable prop => TestName -> prop -> TestTree
testProp s p = testProperty s $ withMaxSuccess numberOfTests p

-- Standard properties of a partial order
lte_reflexive :: Integer -> Property
lte_reflexive (integer -> a) =
  evalOkTrue $ lessThanEqualsInteger a a

lte_antisymmetric :: Integer -> Integer -> Property
lte_antisymmetric (integer -> a) (integer -> b) =
  evalOkTrue $
    (lessThanEqualsInteger a b `and` lessThanEqualsInteger b a) `implies` equalsInteger a b

lte_transitive :: Integer -> Integer -> Integer -> Property
lte_transitive (integer -> a) (integer -> b) (integer -> c) =
  evalOkTrue $
    (lessThanEqualsInteger a b `and` lessThanEqualsInteger b c) `implies` lessThanEqualsInteger a c

trichotomy :: Integer -> Integer -> Property
trichotomy (integer -> a) (integer -> b) =
  evalOkTrue $
    lessThanInteger a b `xor` equalsInteger a b `xor` lessThanInteger b a

-- This establishes a connection between < and <=, allowing us to limit
-- ourselves to checking properties of <=.
lt_versus_lte :: Integer -> Integer -> Property
lt_versus_lte (integer -> a) (integer -> b) =
  evalOkTrue $
    lessThanEqualsInteger a b `iff` (lessThanInteger a b `xor` equalsInteger a b)

-- a <= b and c <= d => a+c <= b+d.  In conjunction with the ring properties
-- this implies, for example, that the sum of two positive integers is positive
-- and the sum of two negative integers is negative, and that a <= a+k for
-- positive k.
add_pairs :: Integer -> Integer -> Integer -> Integer -> Property
add_pairs (integer -> a) (integer -> b) (integer -> c) (integer -> d) =
  evalOkTrue $
    (lessThanEqualsInteger a b `and` lessThanEqualsInteger c d)
    `implies` lessThanEqualsInteger (addInteger a c) (addInteger b d)

-- Test that the signs of various types of product are correct.
mul_pos_pos :: NonNegative Integer -> NonNegative Integer -> Property
mul_pos_pos (NonNegative (integer -> a)) (NonNegative (integer -> b)) =
  evalOkTrue $ lessThanEqualsInteger zero (multiplyInteger a b)

mul_pos_neg :: NonNegative Integer -> NonPositive Integer -> Property
mul_pos_neg (NonNegative (integer -> a)) (NonPositive (integer -> b)) =
  evalOkTrue $ lessThanEqualsInteger (multiplyInteger a b) zero

mul_neg_pos :: NonPositive Integer -> NonNegative Integer -> Property
mul_neg_pos (NonPositive (integer -> a)) (NonNegative (integer -> b)) =
  evalOkTrue $ lessThanEqualsInteger (multiplyInteger a b) zero

mul_neg_neg :: NonPositive Integer -> NonPositive Integer -> Property
mul_neg_neg (NonPositive (integer -> a)) (NonPositive (integer -> b)) =
  evalOkTrue $ lessThanEqualsInteger zero (multiplyInteger a b)

test_integer_order_properties :: TestTree
test_integer_order_properties =
  testGroup "Property tests involving integer ordering"
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
