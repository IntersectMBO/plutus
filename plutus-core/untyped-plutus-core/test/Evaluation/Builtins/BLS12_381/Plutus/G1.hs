{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.BLS12_381.Plutus.G1 (tests)
where

import Control.Monad (when)
import Data.ByteString as BS (length)
import Data.List (foldl', genericReplicate)

import Hedgehog
import Hedgehog.Gen qualified as Gen

import Test.Tasty
import Test.Tasty.Hedgehog

import Evaluation.Builtins.BLS12_381.Common
import PlutusCore.Default


---------------- G1 is an Abelian group ----------------

prop_G1_assoc :: TestTree
prop_G1_assoc =
    testPropertyNamed
    "Addition in G1 is associative"
    "G1_assoc" .
    withNTests $ property $ do
      p1 <- g1elt <$> forAll genG1element
      p2 <- g1elt <$> forAll genG1element
      p3 <- g1elt <$> forAll genG1element
      let e = eqG1 (addG1 p1 (addG1 p2 p3)) (addG1 (addG1 p1 p2) p3)
      evalTerm e === uplcTrue

prop_G1_abelian :: TestTree
prop_G1_abelian =
    testPropertyNamed
    "Addition in G1 is commutative"
    "G1_abelian" .
    withNTests $ property $ do
      p1 <- g1elt <$> forAll genG1element
      p2 <- g1elt <$> forAll genG1element
      let e = eqG1 (addG1 p1 p2) (addG1 p2 p1)
      evalTerm e === uplcTrue

prop_G1_mul :: TestTree
prop_G1_mul =
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

prop_G1_zero :: TestTree
prop_G1_zero =
    testPropertyNamed
    "The point at infinity is an additive identity in G1"
    "G1_zero" .
    withNTests $ property $ do
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (addG1 p zeroG1) p
      evalTerm e === uplcTrue

prop_G1_neg :: TestTree
prop_G1_neg =
    testPropertyNamed
    "Every point in G1 has an additive inverse"
    "G1_inverse" .
    withNTests $ property $ do
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (addG1 p (negG1 p)) zeroG1
      evalTerm e === uplcTrue

test_G1_is_an_Abelian_group :: TestTree
test_G1_is_an_Abelian_group =
    testGroup "G1 is an Abelian group"
         [ prop_G1_assoc
         , prop_G1_zero
         , prop_G1_neg
         , prop_G1_abelian
         ]

---------------- Z acts on G1 correctly ----------------

prop_G1_scalar_inverse :: TestTree
prop_G1_scalar_inverse =
    testPropertyNamed
    "-p = (-1)*p for all p in G1"
    "G1_scalar_inverse" .
    withNTests $ property $ do
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (mulG1 (integer (-1)) p) (negG1 p)
      evalTerm e === uplcTrue

prop_G1_scalar_identity :: TestTree
prop_G1_scalar_identity =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G1"
    "G1_scalar_identity" .
    withNTests $ property $ do
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (mulG1 (integer 1) p) p
      evalTerm e === uplcTrue

prop_G1_scalar_zero :: TestTree
prop_G1_scalar_zero =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G1"
    "G1_scalar_zero" .
    withNTests $ property $ do
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (mulG1 (integer 0) p) zeroG1
      evalTerm e === uplcTrue

prop_G1_scalar_assoc :: TestTree
prop_G1_scalar_assoc =
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

prop_G1_scalar_distributive :: TestTree
prop_G1_scalar_distributive =
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

test_G1_Z_action_good :: TestTree
test_G1_Z_action_good =
    testGroup "Z acts correctly on G1"
         [ prop_G1_scalar_zero
         , prop_G1_scalar_inverse
         , prop_G1_scalar_assoc
         , prop_G1_scalar_distributive
         , prop_G1_scalar_identity
         , prop_G1_mul
         ]


---------------- Compression, uncompression, and hashing work properly ----------------

prop_G1_roundtrip_compression :: TestTree
prop_G1_roundtrip_compression =
    testPropertyNamed
    "Compression followed by uncompression is the identity function on G1"
    "G1_roundtrip_compression" .
    withNTests $ property $ do
      p <- g1elt <$> forAll genG1element
      let e = eqG1 (uncompressG1 (compressG1 p)) p
      evalTerm e === uplcTrue

prop_G1_uncompression_input_size :: TestTree
prop_G1_uncompression_input_size =
    testPropertyNamed
    "G1 uncompression fails if the input has length not equal to 48"
    "G1_uncompression_input_size" .
    withTests 1000 $ property $ do
      b <- bytestring <$> (forAll $ Gen.filter (\x -> BS.length x /= 48) genByteString100)
      let e = uncompressG1 b
      evalTerm e === Nothing

prop_G1_hash :: TestTree
prop_G1_hash =
    testPropertyNamed
    "Different inputs hash to different points in G1"
    "G1_no_hash_collisions" .
    withNTests $ property $ do
      b1 <- bytestring <$> forAll genByteString
      b2 <- bytestring <$> forAll genByteString
      when (b1 /= b2) $ do
           let e = eqG1 (hashToCurveG1 b1) (hashToCurveG1 b2)
           annotateShow e
           evalTerm e === uplcFalse

test_G1_compress_hash :: TestTree
test_G1_compress_hash =
    testGroup "Uncompression and hashing behave properly for G1"
         [ prop_G1_roundtrip_compression
         , prop_G1_uncompression_input_size
         , prop_G1_hash
         ]

-- All the tests

tests :: TestTree
tests =
    testGroup "G1"
        [ test_G1_is_an_Abelian_group
        , test_G1_Z_action_good
        , test_G1_compress_hash
        ]

