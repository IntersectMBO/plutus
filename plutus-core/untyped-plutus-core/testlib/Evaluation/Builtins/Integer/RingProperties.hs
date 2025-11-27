-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

-- | Property tests for the `addInteger`, `subtractInteger`, and `multiplyInteger` builtins
module Evaluation.Builtins.Integer.RingProperties (test_integer_ring_properties)
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck

-- a+(b+c) = (a+b)+c
prop_addition_associative :: BigInteger -> BigInteger -> BigInteger -> Property
prop_addition_associative (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  let t1 = addInteger a (addInteger b c)
      t2 = addInteger (addInteger a b) c
   in evalOkEq t1 t2

-- a+b = b+a
prop_addition_commutative :: BigInteger -> BigInteger -> Property
prop_addition_commutative (biginteger -> a) (biginteger -> b) =
  evalOkEq (addInteger a b) (addInteger b a)

-- a+0 = a
prop_zero_additive_identity :: BigInteger -> Property
prop_zero_additive_identity (biginteger -> a) =
  evalOkEq (addInteger a zero) a

-- (a+b)-b = a
prop_add_subtract_inverse :: BigInteger -> BigInteger -> Property
prop_add_subtract_inverse (biginteger -> a) (biginteger -> b) =
  evalOkEq (subtractInteger (addInteger a b) b) a

-- a*(b*c) = (a*b)*c
prop_multiplication_associative :: BigInteger -> BigInteger -> BigInteger -> Property
prop_multiplication_associative (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  let t1 = multiplyInteger a (multiplyInteger b c)
      t2 = multiplyInteger (multiplyInteger a b) c
   in evalOkEq t1 t2

-- a*b = b*a
prop_multiplication_commutative :: BigInteger -> BigInteger -> Property
prop_multiplication_commutative (biginteger -> a) (biginteger -> b) =
  let t1 = multiplyInteger a b
      t2 = multiplyInteger b a
   in evalOkEq t1 t2

-- a*1 = a
prop_one_multiplicative_identity :: BigInteger -> Property
prop_one_multiplicative_identity (biginteger -> a) =
  let t = multiplyInteger a one
   in evalOkEq t a

-- a*(b+c) = a*b + a*c
prop_distibutive :: BigInteger -> BigInteger -> BigInteger -> Property
prop_distibutive (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  let t1 = multiplyInteger a (addInteger b c)
      t2 = addInteger (multiplyInteger a b) (multiplyInteger a c)
   in evalOkEq t1 t2

test_integer_ring_properties :: TestTree
test_integer_ring_properties =
  testGroup
    "Ring properties for integer arithmetic builtins"
    [ testProperty "addInteger is associative" prop_addition_associative
    , testProperty "addInteger is commutative" prop_addition_commutative
    , testProperty "0 is an identity element for addInteger" prop_zero_additive_identity
    , testProperty "subtraction is the inverse of addition" prop_add_subtract_inverse
    , testProperty "multiplyInteger is associative" prop_multiplication_associative
    , testProperty "multiplyInteger is commutative" prop_multiplication_commutative
    , testProperty "1 is a multiplicative identity" prop_one_multiplicative_identity
    , testProperty "multiplyInteger distributes over addInteger" prop_distibutive
    ]
