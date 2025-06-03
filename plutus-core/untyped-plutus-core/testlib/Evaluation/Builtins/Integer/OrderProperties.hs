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

withNTests :: Testable prop => prop -> Property
withNTests = withMaxSuccess 100

lessThanIrreflexive  :: Integer -> Integer -> Property
lessThanIrreflexive (integer -> a) (integer -> b) =
  undefined

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

  a > 0 and b > 0 => a+b > 0
  a < 0 and b < 0 => a+b < 0

  a > 0 and b > 0 => a*b > 0
  a > 0 and b < 0 => a*b < 0
  a < 0 and b < 0 => a*b > 0
  a < 0 and b > 0 => a*b < 0

  a >= 0 and b >= 0 => a+b >= 0
  a <= 0 and b <= 0 => a+b <= 0

  a >= 0 and b >= 0 => a*b >= 0
  a >= 0 and b <= 0 => a*b <= 0
  a <= 0 and b <= 0 => a*b >= 0
  a <= 0 and b >= 0 => a*b <= 0
-}


test_integer_order_properties :: TestTree
test_integer_order_properties =
  let testProp s p = testProperty s $ withNTests p
  in
  testGroup "Property tests for lessThanInteger and lessThanEqualsInteger"
  []
