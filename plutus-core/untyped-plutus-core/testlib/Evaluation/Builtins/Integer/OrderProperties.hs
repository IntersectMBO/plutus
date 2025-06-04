-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

{- | Property tests for the `lessThanInteger` and `lessThanEqualsInteger` builtins -}
module Evaluation.Builtins.Integer.OrderProperties (test_integer_order_properties)
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common as C

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

import Prelude hiding (and, not, or)

numberOfTests :: Int
numberOfTests = 250

testProp :: Testable prop => TestName -> prop -> TestTree
testProp s p = testProperty s $ withMaxSuccess numberOfTests p

lteReflexive  :: Integer -> Property
lteReflexive (integer -> a) =
  evalOkTrue $ lessThanEqualsInteger a a

lteReflexive2  :: Integer -> Integer -> Property
lteReflexive2 (integer -> a) (integer -> b) =
  evalOkTrue $ lessThanEqualsInteger a b `implies` (not $ lessThanInteger b a)

lteAntisymmetric  :: Integer -> Integer -> Property
lteAntisymmetric (integer -> a) (integer -> b) =
  evalOkTrue $ (lessThanEqualsInteger a b `and` lessThanEqualsInteger b a) `implies` equalsInteger a b

lteTransitive :: Integer -> Integer -> Integer -> Property
lteTransitive (integer -> a) (integer -> b) (integer -> c) =
    evalOkTrue $ (lessThanEqualsInteger a b `and` lessThanEqualsInteger b c) `implies` lessThanEqualsInteger a c

ltVersusLte :: Integer -> Integer -> Property
ltVersusLte (integer -> a) (integer -> b) =
    evalOkTrue $ lessThanEqualsInteger a b `iff` (lessThanInteger a b `xor` equalsInteger a b)

trichotomy :: Integer -> Integer -> Property
trichotomy (integer -> a) (integer -> b) =
    evalOkTrue $ lessThanInteger a b `xor` equalsInteger a b `xor` lessThanInteger b a

add :: Integer -> Integer -> Integer -> Integer -> Property
add (integer -> a) (integer -> b) (integer -> c) (integer -> d) =
    evalOkTrue $
      (lessThanEqualsInteger a b `and` lessThanEqualsInteger c d)
      `implies` lessThanEqualsInteger (addInteger a c) (addInteger b d)

add_pos :: Integer -> NonNegative Integer -> Property
add_pos (integer -> a) (NonNegative (integer -> k)) =
    evalOkTrue $ lessThanEqualsInteger a (addInteger a k)

add_neg :: Integer -> NonPositive Integer -> Property
add_neg (integer -> a) (NonPositive (integer -> k)) =
    evalOkTrue $ lessThanEqualsInteger (addInteger a k) a

add_pos_pos :: NonNegative Integer -> NonNegative Integer -> Property
add_pos_pos (NonNegative (integer -> a)) (NonNegative (integer -> b)) =
    evalOkTrue $ lessThanEqualsInteger zero (addInteger a b)

add_neg_neg :: NonPositive Integer -> NonPositive Integer -> Property
add_neg_neg (NonPositive (integer -> a)) (NonPositive (integer -> b)) =
    evalOkTrue $ lessThanEqualsInteger (addInteger a b) zero

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
  testGroup "Property tests for lessThanInteger and lessThanEqualsInteger"
    [ testProp "lessThanEqualsInteger is reflexive" lteReflexive
    , testProp "lessThanEqualsInteger is reflexive 2" lteReflexive2
    , testProp "lessThanEqualsInteger is antisymmetric" lteAntisymmetric
    , testProp "lessThanEqualsInteger is transitive" lteTransitive
    , testProp "a <= b <=> a < b or a = b" ltVersusLte
    , testProp "a < b or a = b or b < a" trichotomy
    , testProp "add" add
    , testProp "k >= 0 => addInteger a k >= a" add_pos
    , testProp "k <= 0 => addInteger a k <= a" add_neg
    , testProp "addInteger (>= 0) (>= 0) >= 0" add_pos_pos
    , testProp "addInteger (<= 0) (<= 0) <= 0" add_neg_neg
    , testProp "multiplyInteger (>= 0) (>= 0) >= 0" mul_pos_pos
    , testProp "multiplyInteger (>= 0) (<= 0) <= 0" mul_pos_neg
    , testProp "multiplyInteger (<= 0) (>= 0) <= 0" mul_neg_pos
    , testProp "multiplyInteger (<= 0) (<= 0) >= 0" mul_neg_neg
    ]

