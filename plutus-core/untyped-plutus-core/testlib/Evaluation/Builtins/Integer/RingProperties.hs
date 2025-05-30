-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

{- | Property tests for the `addInteger`, `subtractInteger`, and `multiplyInteger` builtins -}
module Evaluation.Builtins.Integer.RingProperties (test_integer_ring_properties)
where

import Evaluation.Builtins.Common

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (builtin, mkIterAppNoAnn)

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

addInteger :: PlcTerm -> PlcTerm -> PlcTerm
addInteger a b = mkIterAppNoAnn (builtin () PLC.AddInteger) [a, b]

subtractInteger :: PlcTerm -> PlcTerm -> PlcTerm
subtractInteger a b = mkIterAppNoAnn (builtin () PLC.SubtractInteger) [a, b]

multiplyInteger :: PlcTerm -> PlcTerm -> PlcTerm
multiplyInteger a b = mkIterAppNoAnn (builtin () PLC.MultiplyInteger) [a, b]

-- a+(b+c) = (a+b)+c
prop_addition_associative :: Integer -> Integer -> Integer -> Property
prop_addition_associative (integer -> a) (integer -> b) (integer -> c) =
  let t1 = addInteger a (addInteger b c)
      t2 = addInteger (addInteger a b) c
  in evalOkEq t1 t2

-- a+b = b+a
prop_addition_commutative :: Integer -> Integer -> Property
prop_addition_commutative (integer -> a) (integer -> b) =
  evalOkEq (addInteger a b) (addInteger b a)

-- a+0 = a
prop_zero_additive_identity :: Integer -> Property
prop_zero_additive_identity (integer -> a) =
  evalOkEq (addInteger a zero) a

-- (a+b)-b = a
prop_add_subtract_inverse :: Integer -> Integer -> Property
prop_add_subtract_inverse (integer -> a) (integer -> b) =
  evalOkEq (subtractInteger (addInteger a b) b) a

-- a*(b*c) = (a*b)*c
prop_multiplication_associative :: Integer -> Integer -> Integer -> Property
prop_multiplication_associative (integer -> a) (integer -> b) (integer -> c) =
  let t1 = multiplyInteger a (multiplyInteger b c)
      t2 = multiplyInteger (multiplyInteger a b) c
  in evalOkEq t1 t2

-- a*b = b*a
prop_multiplication_commutative :: Integer -> Integer -> Property
prop_multiplication_commutative (integer -> a) (integer -> b) =
  let t1 = multiplyInteger a b
      t2 = multiplyInteger b a
  in evalOkEq t1 t2

-- a*1 = a
prop_one_multiplicative_identity :: Integer -> Property
prop_one_multiplicative_identity (integer -> a) =
  let t = multiplyInteger a one
  in evalOkEq t a

-- a*(b+c) = a*b + a*c
prop_distibutive :: Integer -> Integer -> Integer -> Property
prop_distibutive (integer -> a) (integer -> b) (integer -> c) =
  let t1 = multiplyInteger a (addInteger b c)
      t2 = addInteger (multiplyInteger a b) (multiplyInteger a c)
  in evalOkEq t1 t2

test_integer_ring_properties :: TestTree
test_integer_ring_properties =
  testGroup "Ring properties for integer arithmetic builtins"
  [ testProperty "addInteger is associative" prop_addition_associative
  , testProperty "addInteger is commutative" prop_addition_commutative
  , testProperty "0 is an identity element for addInteger" prop_zero_additive_identity
  , testProperty "subtraction is the inverse of addition" prop_add_subtract_inverse
  , testProperty "multiplyInteger is associative" prop_multiplication_associative
  , testProperty "multiplyInteger is commutative" prop_multiplication_commutative
  , testProperty "1 is a multiplicative identity" prop_one_multiplicative_identity
  , testProperty "multiplyInteger distributes over addInteger" prop_distibutive
  ]
