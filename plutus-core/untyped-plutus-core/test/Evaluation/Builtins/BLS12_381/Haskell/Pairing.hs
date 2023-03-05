{-# LANGUAGE OverloadedStrings #-}

module Evaluation.Builtins.BLS12_381.Haskell.Pairing (tests)
where


import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2
import PlutusCore.BLS12_381.GT qualified as GT

import Control.Monad (when)

import Hedgehog

import Test.Tasty
import Test.Tasty.Hedgehog

import Evaluation.Builtins.BLS12_381.Common


---------------- Pairing tests ----------------

pairing :: G1.Element -> G2.Element -> GT.Element
pairing p q =
    case GT.pairing p q of
      Left e  -> error $ show e
      Right r -> r

-- <p1+p2,q> = <p1,q>.<p2,q>
prop_pairing_left_additive :: TestTree
prop_pairing_left_additive =
    testPropertyNamed
    "Pairing is left additive"
    "pairing_left_additive" .
    withNTests $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      q <- forAll genG2element
      let e1 = pairing (G1.add p1 p2) q
          e2 = GT.mul (pairing p1 q) (pairing p2 q)
      GT.finalVerify e1 e2 === True

-- <p,q1+q2> = <p,q1>.<p,q2>
prop_pairing_right_additive :: TestTree
prop_pairing_right_additive =
    testPropertyNamed
    "Pairing is right additive"
    "pairing_right_additive" .
    withNTests $ property $ do
      p <- forAll genG1element
      q1 <- forAll genG2element
      q2 <- forAll genG2element
      let e1 = pairing p (G2.add q1 q2)
          e2 = GT.mul (pairing p q1) (pairing p q2)
      GT.finalVerify e1 e2 === True

-- <[n]p,q> = <p,[n]q> for all n in Z, p in G1, q in G2.
-- We could also test that both of these are equal to <p,q>^n, but we don't have
-- an exponentiation function in GT.  We could implement exponentiation using GT
-- multiplication, but that would require some work.
prop_pairing_balanced :: TestTree
prop_pairing_balanced =
     testPropertyNamed
     "Pairing is balanced"
     "pairing_balanced" .
     withTests 100 $ property $ do
       n <- forAll genScalar
       p <- forAll genG1element
       q <- forAll genG2element
       GT.finalVerify (pairing (G1.mul n p) q) (pairing p (G2.mul n q)) === True

prop_random_pairing :: TestTree
prop_random_pairing =
    testPropertyNamed
    "Pairings of random points are unequal"
    "pairing_random" .
    withNTests $ property $ do
       a <- forAll genG1element
       b <- forAll genG2element
       a' <- forAll genG1element
       b' <- forAll genG2element
       let x = case GT.pairing a b of
                 Left e   -> error $ show e
                 Right xx -> xx
       let y = case GT.pairing a' b' of
                 Left e   -> error $ show e
                 Right yy -> yy
       when (a /= a' || b /= b') $ (GT.finalVerify x y === False)


tests :: TestTree
tests =
    testGroup "Pairing"
        [ prop_pairing_left_additive
        , prop_pairing_right_additive
        , prop_pairing_balanced
        , prop_random_pairing
        ]

