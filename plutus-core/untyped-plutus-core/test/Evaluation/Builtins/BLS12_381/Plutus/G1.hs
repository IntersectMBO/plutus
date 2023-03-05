{-# LANGUAGE OverloadedStrings #-}

module Evaluation.Builtins.BLS12_381.Plutus.G1 (tests)
where

import Data.ByteString as BS (length)
import Data.List (foldl', genericReplicate)

import Hedgehog
import Hedgehog.Gen qualified as Gen

import Test.Tasty
import Test.Tasty.Hedgehog

import Evaluation.Builtins.BLS12_381.Common
import PlutusCore.Default


---------------- G1 is an Abelian group ----------------

prop_assoc :: TestTree
prop_assoc =
    testPropertyNamed
    "Addition in G1 is associative"
    "G1_assoc" .
    withNTests $ property $ do
      p1 <- g1elt <$> forAll genG1element
      p2 <- g1elt <$> forAll genG1element
      p3 <- g1elt <$> forAll genG1element
      let e = eqG1 (addG1 p1 (addG1 p2 p3)) (addG1 (addG1 p1 p2) p3)
      evalTerm e === uplcTrue

prop_zero :: TestTree
prop_zero =
    testPropertyNamed
    "The point at infinity is the additive identity in G1"
    "G1_zero" .
    withNTests $ property $ do
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (addG1 p zeroG1) p
      evalTerm e === uplcTrue

prop_neg :: TestTree
prop_neg =
    testPropertyNamed
    "Every point in G1 has an additive inverse"
    "G1_inverse" .
    withNTests $ property $ do
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (addG1 p (negG1 p)) zeroG1
      evalTerm e === uplcTrue

prop_abelian :: TestTree
prop_abelian =
    testPropertyNamed
    "Addition in G1 is commutative"
    "G1_abelian" .
    withNTests $ property $ do
      p1 <- g1elt <$> forAll genG1element
      p2 <- g1elt <$> forAll genG1element
      let e = eqG1 (addG1 p1 p2) (addG1 p2 p1)
      evalTerm e === uplcTrue

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
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (mulG1 (integer (-1)) p) (negG1 p)
      evalTerm e === uplcTrue

prop_scalar_identity :: TestTree
prop_scalar_identity =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G1"
    "G1_scalar_identity" .
    withNTests $ property $ do
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (mulG1 (integer 1) p) p
      evalTerm e === uplcTrue

prop_scalar_zero :: TestTree
prop_scalar_zero =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G1"
    "G1_scalar_zero" .
    withNTests $ property $ do
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (mulG1 (integer 0) p) zeroG1
      evalTerm e === uplcTrue

prop_scalar_assoc :: TestTree
prop_scalar_assoc =
    testPropertyNamed
    "Scalar multiplication is associative in G1"
    "G1_scalar_assoc" .
    withNTests $ property $ do
      a <- integer <$> forAll genScalar
      b <- integer <$> forAll genScalar
      p <- g1elt   <$> forAll genG1element
      let e1 = mulG1 (mkApp2 MultiplyInteger a b) p
          e2 = mulG1 a (mulG1 b p)
          e3 = eqG1 e1 e2
      evalTerm e3 === uplcTrue

prop_scalar_distributive :: TestTree
prop_scalar_distributive =
    testPropertyNamed
    "Scalar multiplication distributes over addition in G1"
    "G1_scalar_distributive" .
    withNTests $ property $ do
      a <- integer <$> forAll genScalar
      b <- integer <$> forAll genScalar
      p <- g1elt   <$> forAll genG1element
      let e1 = mulG1 (mkApp2 AddInteger a b) p
          e2 = addG1 (mulG1 a p) (mulG1 b p)
          e3 = eqG1 e1 e2
      evalTerm e3 === uplcTrue

prop_scalar_multiplication :: TestTree
prop_scalar_multiplication =
    testPropertyNamed
    "Scalar multiplication is repeated addition in G1"
    "G1_scalar_multiplication" .
    withNTests $ property $ do
      n <- forAll genSmallScalar
      p <- g1elt <$> forAll genG1element
      let e1 = repeatedAddG1 n p
          e2 = eqG1 (mulG1 (integer n) p) e1
      evalTerm e2 === uplcTrue
          where
            repeatedAddG1 :: Integer -> PlcTerm -> PlcTerm
            repeatedAddG1 n t =
                if n>=0
                then foldl' addG1 zeroG1 $ genericReplicate n t
                else repeatedAddG1 (-n) (negG1 t)

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
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (uncompressG1 (compressG1 p)) p
      evalTerm e === uplcTrue

prop_uncompression_input_size :: TestTree
prop_uncompression_input_size =
    testPropertyNamed
    "G1 uncompression fails if the input has length not equal to 48"
    "G1_uncompression_input_size" .
    withTests 1000 $ property $ do
      b <- bytestring <$> (forAll $ Gen.filter (\x -> BS.length x /= 48) genByteString100)
      let e = uncompressG1 b
      evalTerm e === Nothing

prop_hash :: TestTree
prop_hash =
    testPropertyNamed
    "Different inputs hash to different points in G1"
    "G1_no_hash_collisions" .
    withNTests $ property $ do
      b1 <- forAll genByteString
      b2 <- forAll $ Gen.filter (/= b1) genByteString
      let e = eqG1 (hashToCurveG1 $ bytestring b1) (hashToCurveG1 $ bytestring b2)
      evalTerm e === uplcFalse

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

