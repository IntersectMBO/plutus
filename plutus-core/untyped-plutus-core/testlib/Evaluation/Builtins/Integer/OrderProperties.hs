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

withNTests :: Testable prop => prop -> Property
withNTests = withMaxSuccess 100

lteReflexive  :: Integer -> Property
lteReflexive (integer -> a) =
  let t = lessThanEqualsInteger a a
  in evalOkTrue t

lteAntisymmetric  :: Integer -> Integer -> Property
lteAntisymmetric (integer -> a) (integer -> b) =
  let t = ((lessThanEqualsInteger a b) `and` (lessThanEqualsInteger b a)) `implies` (equalsInteger a b)
  in evalOkTrue t

lteTransitive :: Integer -> Integer -> Integer -> Property
lteTransitive (integer -> a) (integer -> b) (integer -> c) =
    let t = ((lessThanEqualsInteger a b) `and` (lessThanEqualsInteger b c)) `implies` (lessThanEqualsInteger a c)
    in evalOkTrue t

ltVersusLte :: Integer -> Integer -> Property
ltVersusLte (integer -> a) (integer -> b) =
    let t = (lessThanEqualsInteger a b) `iff` ((lessThanInteger a b) `xor` (equalsInteger a b))
    in evalOkTrue t

trichotomy :: Integer -> Integer -> Property
trichotomy (integer -> a) (integer -> b) =
    let t1 = lessThanInteger a b
        t2 = equalsInteger a b
        t3 = lessThanInteger b a
    in evalOkTrue (t1 `xor` t2 `xor` t3)

add_pos :: Integer -> NonNegative Integer -> Property
add_pos (integer -> a) (NonNegative (integer -> k)) =
    let t = lessThanEqualsInteger a (addInteger a k)
    in evalOkTrue t

add_neg :: Integer -> NonPositive Integer -> Property
add_neg (integer -> a) (NonPositive (integer -> k)) =
    let t = lessThanEqualsInteger (addInteger a k) a
    in evalOkTrue t

add_pos_pos :: NonNegative Integer -> NonNegative Integer -> Property
add_pos_pos (NonNegative (integer -> a)) (NonNegative (integer -> b)) =
    let t = lessThanEqualsInteger zero (addInteger a b)
    in evalOkTrue t

add_neg_neg :: NonPositive Integer -> NonPositive Integer -> Property
add_neg_neg (NonPositive (integer -> a)) (NonPositive (integer -> b)) =
    let t = lessThanEqualsInteger (addInteger a b) zero
    in evalOkTrue t

mul_pos_pos :: NonNegative Integer -> NonNegative Integer -> Property
mul_pos_pos (NonNegative (integer -> a)) (NonNegative (integer -> b)) =
    let t = lessThanEqualsInteger zero (multiplyInteger a b)
    in evalOkTrue t

mul_pos_neg :: NonNegative Integer -> NonPositive Integer -> Property
mul_pos_neg (NonNegative (integer -> a)) (NonPositive (integer -> b)) =
    let t = lessThanEqualsInteger (multiplyInteger a b) zero
    in evalOkTrue t

mul_neg_pos :: NonPositive Integer -> NonNegative Integer -> Property
mul_neg_pos (NonPositive (integer -> a)) (NonNegative (integer -> b)) =
    let t = lessThanEqualsInteger (multiplyInteger a b) zero
    in evalOkTrue t

mul_neg_neg :: NonPositive Integer -> NonPositive Integer -> Property
mul_neg_neg (NonPositive (integer -> a)) (NonPositive (integer -> b)) =
    let t = lessThanEqualsInteger zero (multiplyInteger a b)
    in evalOkTrue t
{-
  a = a

  ¬(a < a)

  a < b <=> a <= b and ¬(a=b)

  a < b => ¬ (b<a)
  a < b and b < c => a < c

  a <= a
  a <= b and b <= a => a=b
  a <= b and b <= c => a <= c

  a < b => a+c < b+c for all c
  a < b => ca < cb for all c >= 1
  a < b => ca > cb for all c <= -1

  a <= b => a+c <= b+c for all c
  a <= b => ca <= cb for all c >= 1
  a <= b => ca >= cb for all c <= -1

-}


test_integer_order_properties :: TestTree
test_integer_order_properties =
  let testProp s p = testProperty s $ withNTests p
  in
  testGroup "Property tests for lessThanInteger and lessThanEqualsInteger"
  [ testProp "lessThanEqualsInteger is reflexive" lteReflexive
  , testProp "lessThanEqualsInteger is antisymmetric" lteAntisymmetric
  , testProp "lessThanEqualsInteger is transitive" lteTransitive
  , testProp "lessThanVersusLessThanEquals" ltVersusLte
  , testProp "trichotomy holds" trichotomy
  , testProp "k >= 0 => addInteger a k >= a" add_pos
  , testProp "k <= 0 => addInteger a k <= a" add_neg
  , testProp "addInteger (>= 0) (>= 0) >= 0" add_pos_pos
  , testProp "addInteger (<= 0) (<= 0) <= 0" add_neg_neg
  , testProp "multiplyInteger (>= 0) (>= 0) >= 0" mul_pos_pos
  , testProp "multiplyInteger (>= 0) (<= 0) <= 0" mul_pos_neg
  , testProp "multiplyInteger (<= 0) (>= 0) <= 0" mul_neg_pos
  , testProp "multiplyInteger (<= 0) (<= 0) >= 0" mul_neg_neg
  , testProp "a <= b <=> a < b or a = b" lte1
  , testProp "a <= b <=> a < b or a = b" lte2
  ]
