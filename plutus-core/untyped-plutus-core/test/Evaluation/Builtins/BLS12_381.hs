{-# LANGUAGE OverloadedStrings #-}

module Evaluation.Builtins.BLS12_381
where


import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2
import PlutusCore.BLS12_381.GT qualified as GT

import Control.Monad (when)
import Data.ByteString (ByteString)

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Test.Tasty
import Test.Tasty.Hedgehog

{-
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import Evaluation.Builtins.Common (typecheckEvaluateCek)

import PlutusCore
import PlutusCore.MkPlc (builtin, mkConstant, mkIterApp)

import Text.Show.Pretty (ppShow)
  import Data.Kind (Type)
  import Test.Tasty
  import Test.Tasty.Hedgehog
  import Test.Tasty.HUnit
  import PlutusPrelude
-}


{- TODO:
    * Check that decompression always fails for bytestrings that are too long or too short
    * Check the first three bits of compressed points
    * Unit tests for known values.
-}

genByteString :: Gen ByteString
genByteString = Gen.bytes $ Range.linear 0 100

genG1element :: Gen G1.Element
genG1element = G1.hashToCurve <$> Gen.bytes (Range.linear 0 64)

genG2element :: Gen G2.Element
genG2element = G2.hashToCurve <$> Gen.bytes (Range.linear 0 64)

genScalar :: Gen Integer
genScalar = Gen.integral $ Range.linear (-100) 100

repeatedAddG1 :: Integer -> G1.Element -> G1.Element
repeatedAddG1 n p =
    if n < 0 then go (-n) (G1.neg p) G1.zero
    else go n p G1.zero
        where go k a s =
                  if k == 0 then s
                  else go (k-1) a (G1.add a s)


repeatedAddG2 :: Integer -> G2.Element -> G2.Element
repeatedAddG2 n p =
    if n < 0 then go (-n) (G2.neg p) G2.zero
    else go n p G2.zero
        where go k a s =
                  if k == 0 then s
                  else go (k-1) a (G2.add a s)


---------------- G1 ----------------

prop_G1_assoc :: TestTree
prop_G1_assoc =
    testPropertyNamed
    "Addition in G1 is associative"
    "G1_assoc" .
    withTests 100 $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      p3 <- forAll genG1element
      G1.add p1 (G1.add p2 p3) === G1.add (G1.add p1 p2) p3

prop_G1_abelian :: TestTree
prop_G1_abelian =
    testPropertyNamed
    "Addition in G1 is commutative"
    "G1_abelian" .
    withTests 100 $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      G1.add p1 p2 === G1.add p2 p1

prop_G1_mul :: TestTree
prop_G1_mul =
    testPropertyNamed
    "Scalar multiplication is repeated addition in G1"
    "G1_scalar_multiplication" .
    withTests 100 $ property $ do
      n <- forAll genScalar
      p <- forAll genG1element
      G1.mul n p === repeatedAddG1 n p

prop_G1_zero :: TestTree
prop_G1_zero =
    testPropertyNamed
    "The point at infinity is an additive identity in G1"
    "G1_zero" .
    withTests 100 $ property $ do
      p <- forAll genG1element
      p === G1.add p G1.zero

prop_G1_neg :: TestTree
prop_G1_neg =
    testPropertyNamed
    "Every point in G1 has an additive inverse"
    "G1_inverse" .
    withTests 100 $ property $ do
      p <- forAll genG1element
      G1.add p (G1.neg p) === G1.zero

prop_G1_scalar_inverse :: TestTree
prop_G1_scalar_inverse =
    testPropertyNamed
    "-p = (-1)*p for all p in G1"
    "G1_scalar_inverse" .
    withTests 100 $ property $ do
      p <- forAll genG1element
      G1.neg p === G1.mul (-1) p

prop_G1_scalar_identity :: TestTree
prop_G1_scalar_identity =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G1"
    "G1_scalar_identity" .
    withTests 100 $ property $ do
      p <- forAll genG1element
      G1.mul 1 p === p

prop_G1_scalar_zero :: TestTree
prop_G1_scalar_zero =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G1"
    "G1_scalar_zero" .
    withTests 100 $ property $ do
      p <- forAll genG1element
      G1.mul 0 p === G1.zero

prop_G1_scalar_assoc :: TestTree
prop_G1_scalar_assoc =
    testPropertyNamed
    "Scalar multiplication is associative in G1"
    "G1_scalar_assoc" .
    withTests 100 $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG1element
      G1.mul a (G1.mul b p) === G1.mul (a*b) p

prop_G1_scalar_distributive :: TestTree
prop_G1_scalar_distributive =
    testPropertyNamed
    "Scalar multiplication distributes over addition in G1"
    "G1_scalar_distributive" .
    withTests 100 $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG1element
      G1.mul (a+b) p === G1.add (G1.mul a p) (G1.mul b p)

prop_G1_compression :: TestTree
prop_G1_compression =
    testPropertyNamed
    "Compression followed by unconpression is the identity function on G1"
    "G1_compression_distributive" .
    withTests 100 $ property $ do
      p <- forAll genG1element
      case G1.uncompress (G1.compress p) of
        Left e  -> error $ show e
        Right q -> p === q

prop_G1_hash :: TestTree
prop_G1_hash =
    testPropertyNamed
    "Different inputs hash to different points in G1"
    "G1_no_hash_collisions" .
    withTests 100 $ property $ do
      b1 <- forAll genByteString
      b2 <- forAll genByteString
      when (b1 /= b2) $
           G1.hashToCurve b1 /== G1.hashToCurve b2

test_G1 :: TestTree
test_G1 =
    testGroup "G1"
        [ prop_G1_assoc
        , prop_G1_abelian
        , prop_G1_zero
        , prop_G1_neg
        , prop_G1_scalar_zero
        , prop_G1_scalar_inverse
        , prop_G1_scalar_assoc
        , prop_G1_scalar_distributive
        , prop_G1_scalar_identity
        , prop_G1_mul
        , prop_G1_compression
        , prop_G1_hash
        ]


---------------- G2 ----------------

prop_G2_assoc :: TestTree
prop_G2_assoc =
    testPropertyNamed
    "Addition in G2 is associative"
    "G2_assoc" .
    withTests 100 $ property $ do
      p1 <- forAll genG2element
      p2 <- forAll genG2element
      p3 <- forAll genG2element
      G2.add p1 (G2.add p2 p3) === G2.add (G2.add p1 p2) p3

prop_G2_abelian :: TestTree
prop_G2_abelian =
    testPropertyNamed
    "Addition in G2 is commutative"
    "G2_abelian" .
    withTests 100 $ property $ do
      p1 <- forAll genG2element
      p2 <- forAll genG2element
      G2.add p1 p2 === G2.add p2 p1

prop_G2_mul :: TestTree
prop_G2_mul =
    testPropertyNamed
    "Scalar multiplication is repeated addition in G2"
    "G2_scalar_multiplication" .
    withTests 100 $ property $ do
      n <- forAll genScalar
      p <- forAll genG2element
      G2.mul n p === repeatedAddG2 n p

prop_G2_zero :: TestTree
prop_G2_zero =
    testPropertyNamed
    "The point at infinity is an additive identity in G2"
    "G2_zero" .
    withTests 100 $ property $ do
      p <- forAll genG2element
      p === G2.add p G2.zero

prop_G2_neg :: TestTree
prop_G2_neg =
    testPropertyNamed
    "Every point in G2 has an additive inverse"
    "G2_inverse" .
    withTests 100 $ property $ do
      p <- forAll genG2element
      G2.add p (G2.neg p) === G2.zero

prop_G2_scalar_inverse :: TestTree
prop_G2_scalar_inverse =
    testPropertyNamed
    "-p = (-1)*p for all p in G2"
    "G2_scalar_inverse" .
    withTests 100 $ property $ do
      p <- forAll genG2element
      G2.neg p === G2.mul (-1) p

prop_G2_scalar_identity :: TestTree
prop_G2_scalar_identity =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G2"
    "G2_scalar_identity" .
    withTests 100 $ property $ do
      p <- forAll genG2element
      G2.mul 1 p === p

prop_G2_scalar_zero :: TestTree
prop_G2_scalar_zero =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G2"
    "G2_scalar_zero" .
    withTests 100 $ property $ do
      p <- forAll genG2element
      G2.mul 0 p === G2.zero

prop_G2_scalar_assoc :: TestTree
prop_G2_scalar_assoc =
    testPropertyNamed
    "Scalar multiplication is associative in G2"
    "G2_scalar_assoc" .
    withTests 100 $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG2element
      G2.mul a (G2.mul b p) === G2.mul (a*b) p

prop_G2_scalar_distributive :: TestTree
prop_G2_scalar_distributive =
    testPropertyNamed
    "Scalar multiplication distributes over addition in G2"
    "G2_scalar_distributive" .
    withTests 100 $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG2element
      G2.mul (a+b) p === G2.add (G2.mul a p) (G2.mul b p)

prop_G2_compression :: TestTree
prop_G2_compression =
    testPropertyNamed
    "Compression followed by unconpression is the identity function on G2"
    "G2_compression_distributive" .
    withTests 100 $ property $ do
      p <- forAll genG2element
      case G2.uncompress (G2.compress p) of
        Left e  -> error $ show e
        Right q -> p === q

prop_G2_hash :: TestTree
prop_G2_hash =
    testPropertyNamed
    "Different inputs hash to different points in G2"
    "G2_no_hash_collisions" .
    withTests 100 $ property $ do
      b1 <- forAll genByteString
      b2 <- forAll genByteString
      when (b1 /= b2) $
           G2.hashToCurve b1 /== G2.hashToCurve b2

test_G2 :: TestTree
test_G2 =
    testGroup "G2"
        [ prop_G2_assoc
        , prop_G2_abelian
        , prop_G2_zero
        , prop_G2_neg
        , prop_G2_scalar_zero
        , prop_G2_scalar_inverse
        , prop_G2_scalar_assoc
        , prop_G2_scalar_distributive
        , prop_G2_scalar_identity
        , prop_G2_mul
        , prop_G2_compression
        , prop_G2_hash
        ]

---------------- Pairing ----------------

pairing :: G1.Element -> G2.Element -> GT.Element
pairing p q =
    case GT.millerLoop p q of
      Left e  -> error $ show e
      Right r -> r


-- <p1+p2,q> = <p1,q>.<p2,q>
prop_pairing_left_additive :: TestTree
prop_pairing_left_additive =
    testPropertyNamed
    "Pairing is left additive"
    "pairing_left_additive" .
    withTests 100 $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      q <- forAll genG2element
      GT.finalVerify (pairing (G1.add p1 p2) q) (GT.mul (pairing p1 q) (pairing p2 q)) === True

-- <p,q1+q2> = <p,q1>.<p,q2>
prop_pairing_right_additive :: TestTree
prop_pairing_right_additive =
    testPropertyNamed
    "Pairing is right additive"
    "pairing_right_additive" .
    withTests 100 $ property $ do
      p <- forAll genG1element
      q1 <- forAll genG2element
      q2 <- forAll genG2element
      GT.finalVerify (pairing p (G2.add q1 q2)) (GT.mul (pairing p q1) (pairing p q2)) === True

-- <ap, q> == <p,aq> for all a in Z, p in G1, q in G2
prop_pairing_balanced :: TestTree
prop_pairing_balanced =
    testPropertyNamed
    "Pairing is balanced"
    "pairing_balanced" .
    withTests 100 $ property $ do
      a <- forAll genScalar
      p <- forAll genG1element
      q <- forAll genG2element
      GT.finalVerify (pairing (G1.mul a p) q) (pairing p (G2.mul a q)) === True

prop_random_pairing :: TestTree
prop_random_pairing =
    testPropertyNamed
    "Pairings of random points are unequal"
    "pairing_random" .
    withTests 100 $ property $ do
       a <- forAll genG1element
       b <- forAll genG2element
       a' <- forAll genG1element
       b' <- forAll genG2element
       let x = case GT.millerLoop a b of
                 Left e   -> error $ show e
                 Right xx -> xx
       let y = case GT.millerLoop a' b' of
                 Left e   -> error $ show e
                 Right yy -> yy
       when (a /= a' && b /= b') $ (GT.finalVerify x y === False)


test_pairing :: TestTree
test_pairing =
    testGroup "Pairing"
                  [ prop_pairing_left_additive
                  , prop_pairing_right_additive
                  , prop_pairing_balanced
                  , prop_random_pairing
                  ]


test_BLS12_381 :: TestTree
test_BLS12_381 =
    testGroup "BLS12-381"
    [ test_G1
    , test_G2
    , test_pairing
    ]
