{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.BLS12_381.Plutus.G2 (tests)
where


import Control.Monad (when)
import Data.ByteString as BS (length)
import Data.List (foldl', genericReplicate)

import Hedgehog
import Hedgehog.Gen qualified as Gen

import Test.Tasty
import Test.Tasty.Hedgehog

import Evaluation.Builtins.BLS12_381.Common
import PlutusCore as PLC


---------------- G2 is an Abelian group ----------------

prop_G2_assoc :: TestTree
prop_G2_assoc =
    testPropertyNamed
    "Addition in G2 is associative"
    "G2_assoc" .
    withNTests $ property $ do
      p1 <- g2elt <$> forAll genG2element
      p2 <- g2elt <$> forAll genG2element
      p3 <- g2elt <$> forAll genG2element
      let e = eqG2 (addG2 p1 (addG2 p2 p3)) (addG2 (addG2 p1 p2) p3)
      evalTerm e === uplcTrue

prop_G2_abelian :: TestTree
prop_G2_abelian =
    testPropertyNamed
    "Addition in G2 is commutative"
    "G2_abelian" .
    withNTests $ property $ do
      p1 <- g2elt <$> forAll genG2element
      p2 <- g2elt <$> forAll genG2element
      let e = eqG2 (addG2 p1 p2) (addG2 p2 p1)
      evalTerm e === uplcTrue

prop_G2_mul :: TestTree
prop_G2_mul =
    testPropertyNamed
    "Scalar multiplication is repeated addition in G2"
    "G2_scalar_multiplication" .
    withNTests $ property $ do
      n <- forAll genSmallScalar
      p <- g2elt <$> forAll genG2element
      let e1 = repeatedAddG2 n p
          e2 = eqG2 (mulG2 (integer n) p) e1
      evalTerm e2 === uplcTrue
          where
            repeatedAddG2 :: Integer -> PlcTerm -> PlcTerm
            repeatedAddG2 n t =
                if n>=0
                then foldl' addG2 zeroG2 $ genericReplicate n t
                else repeatedAddG2 (-n) (negG2 t)

prop_G2_zero :: TestTree
prop_G2_zero =
    testPropertyNamed
    "The point at infinity is the additive identity in G2"
    "G2_zero" .
    withNTests $ property $ do
      p <- g2elt <$> forAll genG2element
      let e = eqG2 (addG2 p zeroG2) p
      evalTerm e === uplcTrue

prop_G2_neg :: TestTree
prop_G2_neg =
    testPropertyNamed
    "Every point in G2 has an additive inverse"
    "G2_inverse" .
    withNTests $ property $ do
      p <- g2elt <$> forAll genG2element
      let e = eqG2 (addG2 p (negG2 p)) zeroG2
      evalTerm e === uplcTrue

test_G2_is_an_Abelian_group :: TestTree
test_G2_is_an_Abelian_group =
    testGroup "G2 is an Abelian group"
         [ prop_G2_assoc
         , prop_G2_zero
         , prop_G2_neg
         , prop_G2_abelian
         ]


---------------- Z acts on G2 correctly ----------------

prop_G2_scalar_inverse :: TestTree
prop_G2_scalar_inverse =
    testPropertyNamed
    "-p = (-1)*p for all p in G2"
    "G2_scalar_inverse" .
    withNTests $ property $ do
      p <- g2elt <$> forAll genG2element
      let e = eqG2 (mulG2 (integer (-1)) p) (negG2 p)
      evalTerm e === uplcTrue

prop_G2_scalar_identity :: TestTree
prop_G2_scalar_identity =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G2"
    "G2_scalar_identity" .
    withNTests $ property $ do
      p <- g2elt <$> forAll genG2element
      let e = eqG2 (mulG2 (integer 1) p) p
      evalTerm e === uplcTrue

prop_G2_scalar_zero :: TestTree
prop_G2_scalar_zero =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G2"
    "G2_scalar_zero" .
    withNTests $ property $ do
      p <- g2elt <$> forAll genG2element
      let e = eqG2 (mulG2 (integer 0) p) zeroG2
      evalTerm e === uplcTrue

prop_G2_scalar_assoc :: TestTree
prop_G2_scalar_assoc =
    testPropertyNamed
    "Scalar multiplication is associative in G2"
    "G2_scalar_assoc" .
    withNTests $ property $ do
      a <- integer <$> forAll genScalar
      b <- integer <$> forAll genScalar
      p <- g2elt   <$> forAll genG2element
      let e1 = mulG2 (mkApp2 MultiplyInteger a b) p
          e2 = mulG2 a (mulG2 b p)
          e3 = eqG2 e1 e2
      evalTerm e3 === uplcTrue

prop_G2_scalar_distributive :: TestTree
prop_G2_scalar_distributive =
    testPropertyNamed
    "Scalar multiplication distributes over addition in G2"
    "G2_scalar_distributive" .
    withNTests $ property $ do
      a <- integer <$> forAll genScalar
      b <- integer <$> forAll genScalar
      p <- g2elt   <$> forAll genG2element
      let e1 = mulG2 (mkApp2 AddInteger a b) p
          e2 = addG2 (mulG2 a p) (mulG2 b p)
          e3 = eqG2 e1 e2
      evalTerm e3 === uplcTrue

test_G2_Z_action_good :: TestTree
test_G2_Z_action_good =
    testGroup "Z acts correctly on G2"
         [ prop_G2_scalar_zero
         , prop_G2_scalar_inverse
         , prop_G2_scalar_assoc
         , prop_G2_scalar_distributive
         , prop_G2_scalar_identity
         , prop_G2_mul
         ]


---------------- Compression, uncompression, and hashing work properly ----------------

prop_G2_roundtrip_compression :: TestTree
prop_G2_roundtrip_compression =
    testPropertyNamed
    "Compression followed by uncompression is the identity function on G2"
    "G2_roundtrip_compression" .
    withNTests $ property $ do
      p <- g2elt <$> forAll genG2element
      let e = eqG2 (uncompressG2 (compressG2 p)) p
      evalTerm e === uplcTrue

prop_G2_uncompression_input_size :: TestTree
prop_G2_uncompression_input_size =
    testPropertyNamed
    "G2 uncompression fails if the input has length not equal to 96"
    "G2_uncompression_input_size" .
    withTests 1000 $ property $ do
      b <- bytestring <$> (forAll $ Gen.filter (\x -> BS.length x /= 96) genByteString100)
      let e = uncompressG2 b
      evalTerm e === Nothing

prop_G2_hash :: TestTree
prop_G2_hash =
    testPropertyNamed
    "Different inputs hash to different points in G2"
    "G2_no_hash_collisions" .
    withNTests $ property $ do
      b1 <- bytestring <$> forAll genByteString
      b2 <- bytestring <$> forAll genByteString
      when (b1 /= b2) $ do
           let e = eqG2 (hashToCurveG2 b1) (hashToCurveG2 b2)
           annotateShow e
           evalTerm e === uplcFalse

test_G2_compress_hash :: TestTree
test_G2_compress_hash =
    testGroup "Uncompression and hashing behave properly for G2"
         [ prop_G2_roundtrip_compression
         , prop_G2_uncompression_input_size
         , prop_G2_hash
         ]

-- All the tests

tests :: TestTree
tests =
    testGroup "G2"
        [ test_G2_is_an_Abelian_group
        , test_G2_Z_action_good
        , test_G2_compress_hash
        ]

