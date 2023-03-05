{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.BLS12_381.Plutus.Pairing (tests)
where

import Evaluation.Builtins.BLS12_381.Common

import Control.Monad (when)

import Hedgehog

import Test.Tasty
import Test.Tasty.Hedgehog


-- <p1+p2,q> = <p1,q>.<p2,q>
prop_pairing_left_additive :: TestTree
prop_pairing_left_additive =
    testPropertyNamed
    "Pairing is left additive"
    "pairing_left_additive" .
    withNTests $ property $ do
      p1 <- g1elt <$> forAll genG1element
      p2 <- g1elt <$> forAll genG1element
      q  <- g2elt <$> forAll genG2element
      let e1 = pairingPlc (addG1 p1 p2) q
          e2 = mulGT (pairingPlc p1 q) (pairingPlc p2 q)
          e3 = finalVerifyPlc e1 e2
      evalTerm e3 === uplcTrue

-- <p,q1+q2> = <p,q1>.<p,q2>
prop_pairing_right_additive :: TestTree
prop_pairing_right_additive =
    testPropertyNamed
    "Pairing is right additive"
    "pairing_right_additive" .
    withNTests $ property $ do
      p  <- g1elt <$> forAll genG1element
      q1 <- g2elt <$> forAll genG2element
      q2 <- g2elt <$> forAll genG2element
      let e1 = pairingPlc p (addG2 q1 q2)
          e2 = mulGT (pairingPlc p q1) (pairingPlc p q2)
          e3 = finalVerifyPlc e1 e2
      evalTerm e3 === uplcTrue

prop_pairing_balanced :: TestTree
prop_pairing_balanced =
    testPropertyNamed
    "Pairing is balanced"
    "pairing_balanced" .
    withNTests $ property $ do
      n <- integer <$> forAll genScalar
      p <- g1elt   <$> forAll genG1element
      q <- g2elt   <$> forAll genG2element
      let e1 = pairingPlc (mulG1 n p) q
          e2 = pairingPlc p (mulG2 n q)
          e3 = finalVerifyPlc e1 e2
      evalTerm e3 === uplcTrue

prop_random_pairing :: TestTree
prop_random_pairing =
    testPropertyNamed
    "Pairings of random points are unequal"
    "pairing_random" .
    withNTests $ property $ do
       p1 <- g1elt <$> forAll genG1element
       p2 <- g1elt <$> forAll genG1element
       q1 <- g2elt <$> forAll genG2element
       q2 <- g2elt <$> forAll genG2element
       when (p1 /= p2 || q1  /= q2) $
            let e = finalVerifyPlc (pairingPlc p1 q1) (pairingPlc p2 q2)
            in evalTerm e === uplcFalse

tests :: TestTree
tests =
    testGroup "Pairing"
        [ prop_pairing_left_additive
        , prop_pairing_right_additive
        , prop_pairing_balanced
        , prop_random_pairing
        ]
