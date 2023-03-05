{-# LANGUAGE OverloadedStrings #-}

module Evaluation.Builtins.BLS12_381.Haskell.G1 (tests)
where

import Evaluation.Builtins.BLS12_381.Common
import PlutusCore.BLS12_381.G1 qualified as G1

import Data.ByteString as BS (length)
import Data.Either (isLeft)
import Data.List (foldl', genericReplicate)

import Hedgehog
import Hedgehog.Gen qualified as Gen

import Test.Tasty
import Test.Tasty.Hedgehog


---------------- G1 is an Abelian group ----------------

prop_assoc :: TestTree
prop_assoc =
    testPropertyNamed
    "Addition in G1 is associative"
    "G1_assoc" .
    withNTests $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      p3 <- forAll genG1element
      G1.add p1 (G1.add p2 p3) === G1.add (G1.add p1 p2) p3

prop_zero :: TestTree
prop_zero =
    testPropertyNamed
    "The point at infinity is an additive identity in G1"
    "G1_zero" .
    withNTests $ property $ do
      p <- forAll genG1element
      p === G1.add p G1.zero

prop_neg :: TestTree
prop_neg =
    testPropertyNamed
    "Every point in G1 has an additive inverse"
    "G1_inverse" .
    withNTests $ property $ do
      p <- forAll genG1element
      G1.add p (G1.neg p) === G1.zero

prop_abelian :: TestTree
prop_abelian =
    testPropertyNamed
    "Addition in G1 is commutative"
    "G1_abelian" .
    withNTests $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      G1.add p1 p2 === G1.add p2 p1

test_is_an_Abelian_group :: TestTree
test_is_an_Abelian_group =
    testGroup "G1 is an Abelian group"
         [ prop_assoc
         , prop_zero
         , prop_neg
         , prop_abelian
         ]

---------------- Z acts on G1 correctly ----------------

prop_scalar_inverse :: TestTree
prop_scalar_inverse =
    testPropertyNamed
    "-p = (-1)*p for all p in G1"
    "G1_scalar_inverse" .
    withNTests $ property $ do
      p <- forAll genG1element
      G1.neg p === G1.mul (-1) p

prop_scalar_identity :: TestTree
prop_scalar_identity =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G1"
    "G1_scalar_identity" .
    withNTests $ property $ do
      p <- forAll genG1element
      G1.mul 1 p === p

prop_scalar_zero :: TestTree
prop_scalar_zero =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G1"
    "G1_scalar_zero" .
    withNTests $ property $ do
      p <- forAll genG1element
      G1.mul 0 p === G1.zero

prop_scalar_assoc :: TestTree
prop_scalar_assoc =
    testPropertyNamed
    "Scalar multiplication is associative in G1"
    "G1_scalar_assoc" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG1element
      G1.mul (a*b) p === G1.mul a (G1.mul b p)

prop_scalar_distributive :: TestTree
prop_scalar_distributive =
    testPropertyNamed
    "Scalar multiplication distributes over addition in G1"
    "G1_scalar_distributive" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG1element
      G1.mul (a+b) p === G1.add (G1.mul a p) (G1.mul b p)

prop_scalar_multiplication :: TestTree
prop_scalar_multiplication =
    testPropertyNamed
    "Scalar multiplication is repeated addition in G1"
    "G1_scalar_multiplication" .
    withNTests $ property $ do
      n <- forAll genSmallScalar
      p <- forAll genG1element
      G1.mul n p === repeatedAddG1 n p
          where repeatedAddG1 :: Integer -> G1.Element -> G1.Element
                repeatedAddG1 n p =
                    if n >= 0
                    then foldl' G1.add G1.zero $ genericReplicate n p
                    else repeatedAddG1 (-n) (G1.neg p)

test_Z_action_good :: TestTree
test_Z_action_good =
    testGroup "Z acts correctly on G1"
         [ prop_scalar_zero
         , prop_scalar_inverse
         , prop_scalar_assoc
         , prop_scalar_distributive
         , prop_scalar_identity
         , prop_scalar_multiplication
         ]

---------------- Compression, uncompression, and hashing work properly ----------------

prop_roundtrip_compression :: TestTree
prop_roundtrip_compression =
    testPropertyNamed
    "Compression followed by uncompression is the identity function on G1"
    "G1_roundtrip_compression" .
    withNTests $ property $ do
      p <- forAll genG1element
      case G1.uncompress (G1.compress p) of
        Left e  -> error $ show e
        Right q -> p === q

-- G1.uncompress should only accept inputs of length 48 (but not all inputs of
-- length 48 are valid)
prop_uncompression_input_size :: TestTree
prop_uncompression_input_size =
    testPropertyNamed
    "G1 uncompression fails if the input has length not equal to 48"
    "G1_uncompression_input_size" .
    withTests 1000 $ property $ do
      b <- forAll $ Gen.filter (\x -> BS.length x /= 48) $ genByteString100
      assert $ isLeft $ G1.uncompress b

prop_hash :: TestTree
prop_hash =
    testPropertyNamed
    "Different inputs hash to different points in G1"
    "G1_no_hash_collisions" .
    withNTests $ property $ do
      b1 <- forAll genByteString
      b2 <- forAll $ Gen.filter (/= b1) genByteString  -- Does this do what I think it does?
      G1.hashToCurve b1 /== G1.hashToCurve b2

test_compress_hash :: TestTree
test_compress_hash =
    testGroup "Uncompression and hashing behave properly for G1"
         [ prop_roundtrip_compression
         , prop_uncompression_input_size
         , prop_hash
         ]

-- All the tests

tests :: TestTree
tests =
    testGroup "G1"
        [ test_is_an_Abelian_group
        , test_Z_action_good
        , test_compress_hash
        ]

