{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.BLS12_381
    (test_BLS12_381)
where


import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2
import PlutusCore.BLS12_381.GT qualified as GT

import Control.Monad (when)
import Data.ByteString (ByteString, pack)
import UntypedPlutusCore as UPLC

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Test.Tasty
import Test.Tasty.Hedgehog

import Evaluation.Builtins.Common
import PlutusCore as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults

import PlutusCore.MkPlc (builtin, mkConstant, mkIterApp)

{-

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

withNTests :: Property -> Property
withNTests = withTests 300

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

type PlcTerm = PLC.Term TyName Name DefaultUni DefaultFun ()
type UplcTerm = UPLC.Term Name DefaultUni DefaultFun ()

uplcTrue :: UplcTerm
uplcTrue = mkConstant () True

uplcFalse :: UplcTerm
uplcFalse = mkConstant () False

integer :: Integer -> PlcTerm
integer = mkConstant ()

bytestring :: ByteString -> PlcTerm
bytestring = mkConstant ()

g1elt :: G1.Element ->  PlcTerm
g1elt = mkConstant ()

g2elt :: G2.Element ->  PlcTerm
g2elt = mkConstant ()

mkApp1 :: PlcTerm -> PlcTerm -> PlcTerm
mkApp1 b x = mkIterApp () b [x]

mkApp2 :: PlcTerm -> PlcTerm -> PlcTerm -> PlcTerm
mkApp2 b x y = mkIterApp () b [x,y]

-- Contstructing G1 builtin application terms

addG1 :: PlcTerm -> PlcTerm -> PlcTerm
addG1 = mkApp2 $ builtin () Bls12_381_G1_add

eqG1 :: PlcTerm -> PlcTerm -> PlcTerm
eqG1 = mkApp2 $ builtin () Bls12_381_G1_equal

mulG1 :: PlcTerm -> PlcTerm -> PlcTerm
mulG1 = mkApp2 $ builtin () Bls12_381_G1_mul


negG1 :: PlcTerm -> PlcTerm
negG1 = mkApp1 $ builtin () Bls12_381_G1_neg

uncompressG1 :: PlcTerm -> PlcTerm
uncompressG1 = mkApp1 $ builtin () Bls12_381_G1_uncompress

compressG1 :: PlcTerm -> PlcTerm
compressG1 = mkApp1 $ builtin () Bls12_381_G1_compress

hashToCurveG1 :: PlcTerm -> PlcTerm
hashToCurveG1 = mkApp1 $ builtin () Bls12_381_G1_hashToCurve

zeroG1 :: PlcTerm
zeroG1 =
    let b = bytestring $ pack (0xc0 : replicate 47 0x00)
    in uncompressG1 b

-- Contstructing G2 builtin application terms

addG2 :: PlcTerm -> PlcTerm -> PlcTerm
addG2 = mkApp2 $ builtin () Bls12_381_G2_add

eqG2 :: PlcTerm -> PlcTerm -> PlcTerm
eqG2 = mkApp2 $ builtin () Bls12_381_G2_equal

mulG2 :: PlcTerm -> PlcTerm -> PlcTerm
mulG2 = mkApp2 $ builtin () Bls12_381_G2_mul


negG2 :: PlcTerm -> PlcTerm
negG2 = mkApp1 $ builtin () Bls12_381_G2_neg

uncompressG2 :: PlcTerm -> PlcTerm
uncompressG2 = mkApp1 $ builtin () Bls12_381_G2_uncompress

compressG2 :: PlcTerm -> PlcTerm
compressG2 = mkApp1 $ builtin () Bls12_381_G2_compress

hashToCurveG2 :: PlcTerm -> PlcTerm
hashToCurveG2 = mkApp1 $ builtin () Bls12_381_G2_hashToCurve

zeroG2 :: PlcTerm
zeroG2 =
    let b = bytestring $ pack (0xc0 : replicate 95 0x00)
    in uncompressG2 b

-- Constructing pairing terms

pairingPlc :: PlcTerm -> PlcTerm -> PlcTerm
pairingPlc = mkApp2 $ builtin () Bls12_381_GT_millerLoop

finalVerifyPlc :: PlcTerm -> PlcTerm -> PlcTerm
finalVerifyPlc = mkApp2 $ builtin () Bls12_381_GT_finalVerify

mulGT :: PlcTerm -> PlcTerm -> PlcTerm
mulGT = mkApp2 $ builtin () Bls12_381_GT_mul

-- Evaluating PLC terms

evalTerm
    :: PLC.Term TyName Name DefaultUni DefaultFun ()
    -> UPLC.Term Name DefaultUni DefaultFun ()
evalTerm term =
    case typecheckEvaluateCekNoEmit DefaultFunV1 defaultBuiltinCostModel term
    of Left err -> error $ show err
       Right x  ->
           case x of
             EvaluationFailure   -> error "Evaluation failure"
             EvaluationSuccess s -> s

---------------- G1 tests ----------------

prop_G1_assoc :: TestTree
prop_G1_assoc =
    testPropertyNamed
    "Addition in G1 is associative"
    "G1_assoc" .
    withNTests $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      p3 <- forAll genG1element
      G1.add p1 (G1.add p2 p3) === G1.add (G1.add p1 p2) p3

prop_G1_assoc_plutus :: TestTree
prop_G1_assoc_plutus =
    testPropertyNamed
    "Addition in G1 is associative"
    "G1_assoc_plutus" .
    withNTests $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      p3 <- forAll genG1element
      let e1 = addG1 (g1elt p1) (addG1 (g1elt p2) (g1elt p3))
          e2 = addG1 (addG1 (g1elt p1) (g1elt p2)) (g1elt p3)
          e3 = eqG1 e1 e2
      evalTerm e3 === uplcTrue

prop_G1_abelian :: TestTree
prop_G1_abelian =
    testPropertyNamed
    "Addition in G1 is commutative"
    "G1_abelian" .
    withNTests $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      G1.add p1 p2 === G1.add p2 p1

prop_G1_abelian_plutus :: TestTree
prop_G1_abelian_plutus =
    testPropertyNamed
    "Addition in G1 is commutative"
    "G1_abelian_plutus" .
    withNTests $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      let e1 = addG1 (g1elt p1) (g1elt p2)
          e2 = addG1 (g1elt p2) (g1elt p1)
          e3 = eqG1 e1 e2
      evalTerm e3 === uplcTrue

prop_G1_mul :: TestTree
prop_G1_mul =
    testPropertyNamed
    "Scalar multiplication is repeated addition in G1"
    "G1_scalar_multiplication" .
    withNTests $ property $ do
      n <- forAll genScalar
      p <- forAll genG1element
      G1.mul n p === repeatedAddG1 n p

{-
prop_G1_mul_plutus :: TestTree_plutus
prop_G1_mul_plutus =
    testPropertyNamed
    "Scalar multiplication is repeated addition in G1"
    "G1_scalar_multiplication" .
    withNTests $ property $ do
      n <- forAll genScalar
      p <- forAll genG1element
      G1.mul n p === repeatedAddG1 n p
-}

prop_G1_zero :: TestTree
prop_G1_zero =
    testPropertyNamed
    "The point at infinity is an additive identity in G1"
    "G1_zero" .
    withNTests $ property $ do
      p <- forAll genG1element
      p === G1.add p G1.zero

prop_G1_zero_plutus :: TestTree
prop_G1_zero_plutus =
    testPropertyNamed
    "The point at infinity is an additive identity in G1"
    "G1_zero_plutus" .
    withNTests $ property $ do
      p <- forAll genG1element
      let e1 = addG1 (g1elt p) zeroG1
          e2 = eqG1 (g1elt p) e1
      evalTerm e2 === uplcTrue

prop_G1_neg :: TestTree
prop_G1_neg =
    testPropertyNamed
    "Every point in G1 has an additive inverse"
    "G1_inverse" .
    withNTests $ property $ do
      p <- forAll genG1element
      G1.add p (G1.neg p) === G1.zero

prop_G1_neg_plutus :: TestTree
prop_G1_neg_plutus =
    testPropertyNamed
    "Every point in G1 has an additive inverse"
    "G1_inverse_plutus" .
    withNTests $ property $ do
      p <- forAll genG1element
      let e1 = addG1 (g1elt p) (negG1 (g1elt p))
          e2 = eqG1 e1 zeroG1
      evalTerm e2 === uplcTrue

prop_G1_scalar_inverse :: TestTree
prop_G1_scalar_inverse =
    testPropertyNamed
    "-p = (-1)*p for all p in G1"
    "G1_scalar_inverse" .
    withNTests $ property $ do
      p <- forAll genG1element
      G1.neg p === G1.mul (-1) p

prop_G1_scalar_inverse_plutus :: TestTree
prop_G1_scalar_inverse_plutus =
    testPropertyNamed
    "-p = (-1)*p for all p in G1"
    "G1_scalar_inverse_plutus" .
    withNTests $ property $ do
      p <- forAll genG1element
      let e1 = negG1 (g1elt p)
          e2 = mulG1 (integer (-1)) (g1elt p)
          e3 = eqG1 e1 e2
      evalTerm e3 === uplcTrue

prop_G1_scalar_identity :: TestTree
prop_G1_scalar_identity =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G1"
    "G1_scalar_identity" .
    withNTests $ property $ do
      p <- forAll genG1element
      G1.mul 1 p === p

prop_G1_scalar_identity_plutus :: TestTree
prop_G1_scalar_identity_plutus =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G1"
    "G1_scalar_identity_plutus" .
    withNTests $ property $ do
      p <- forAll genG1element
      let e = eqG1 (mulG1 (integer 1) (g1elt p)) (g1elt p)
      evalTerm e === uplcTrue

prop_G1_scalar_zero :: TestTree
prop_G1_scalar_zero =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G1"
    "G1_scalar_zero" .
    withNTests $ property $ do
      p <- forAll genG1element
      G1.mul 0 p === G1.zero

prop_G1_scalar_zero_plutus :: TestTree
prop_G1_scalar_zero_plutus =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G1"
    "G1_scalar_zero_plutus" .
    withNTests $ property $ do
      p <- forAll genG1element
      let e1 = mulG1 (integer 0) (g1elt p)
          e2 = eqG1 e1 zeroG1
      evalTerm e2 === uplcTrue

prop_G1_scalar_assoc :: TestTree
prop_G1_scalar_assoc =
    testPropertyNamed
    "Scalar multiplication is associative in G1"
    "G1_scalar_assoc" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG1element
      G1.mul (a*b) p === G1.mul a (G1.mul b p)

prop_G1_scalar_assoc_plutus :: TestTree
prop_G1_scalar_assoc_plutus =
    testPropertyNamed
    "Scalar multiplication is associative in G1"
    "G1_scalar_assoc_plutus" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG1element
      let e1 = mulG1 (mkApp2 (builtin () MultiplyInteger) (integer a) (integer b)) (g1elt p)
          e2 = mulG1 (integer a) (mulG1 (integer b) (g1elt p))
          e3 = eqG1 e1 e2
      evalTerm e3 === uplcTrue

prop_G1_scalar_distributive :: TestTree
prop_G1_scalar_distributive =
    testPropertyNamed
    "Scalar multiplication distributes over addition in G1"
    "G1_scalar_distributive" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG1element
      G1.mul (a+b) p === G1.add (G1.mul a p) (G1.mul b p)

prop_G1_scalar_distributive_plutus :: TestTree
prop_G1_scalar_distributive_plutus =
    testPropertyNamed
    "Scalar multiplication distributes over addition in G1"
    "G1_scalar_distributive_plutus" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG1element
      let e1 = mulG1 (mkApp2 (builtin () AddInteger) (integer a) (integer b)) (g1elt p)
          e2 = addG1 (mulG1 (integer a) (g1elt p))  (mulG1 (integer b) (g1elt p))
          e3 = eqG1 e1 e2
      evalTerm e3 === uplcTrue

prop_G1_compression :: TestTree
prop_G1_compression =
    testPropertyNamed
    "Compression followed by uncompression is the identity function on G1"
    "G1_compression_distributive" .
    withNTests $ property $ do
      p <- forAll genG1element
      case G1.uncompress (G1.compress p) of
        Left e  -> error $ show e
        Right q -> p === q

prop_G1_compression_plutus :: TestTree
prop_G1_compression_plutus =
    testPropertyNamed
    "Compression followed by uncompression is the identity function on G1"
    "G1_compression_distributive_plutus" .
    withNTests $ property $ do
      p <- forAll genG1element
      let e1 = uncompressG1 (compressG1 (g1elt p))
          e2 = eqG1 e1 (g1elt p)
      evalTerm e2 === uplcTrue

prop_G1_hash :: TestTree
prop_G1_hash =
    testPropertyNamed
    "Different inputs hash to different points in G1"
    "G1_no_hash_collisions" .
    withNTests $ property $ do
      b1 <- forAll genByteString
      b2 <- forAll genByteString
      when (b1 /= b2) $
           G1.hashToCurve b1 /== G1.hashToCurve b2

prop_G1_hash_plutus :: TestTree
prop_G1_hash_plutus =
    testPropertyNamed
    "Different inputs hash to different points in G1"
    "G1_no_hash_collisions_plutus" .
    withNTests $ property $ do
      b1 <- forAll genByteString
      b2 <- forAll genByteString
      when (b1 /= b2) $ do
           let e = eqG1 (hashToCurveG1 (bytestring b1)) (hashToCurveG1 (bytestring b2))
           evalTerm e === uplcFalse

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

test_G1_plutus :: TestTree
test_G1_plutus =
    testGroup "G1"
        [ prop_G1_assoc_plutus
        , prop_G1_abelian_plutus
        , prop_G1_zero_plutus
        , prop_G1_neg_plutus
        , prop_G1_scalar_zero_plutus
        , prop_G1_scalar_inverse_plutus
        , prop_G1_scalar_assoc_plutus
        , prop_G1_scalar_distributive_plutus
        , prop_G1_scalar_identity_plutus
        -- , prop_G1_mul_plutus
        , prop_G1_compression_plutus
        , prop_G1_hash_plutus
        ]


---------------- G2 tests ----------------

prop_G2_assoc :: TestTree
prop_G2_assoc =
    testPropertyNamed
    "Addition in G2 is associative"
    "G2_assoc" .
    withNTests $ property $ do
      p1 <- forAll genG2element
      p2 <- forAll genG2element
      p3 <- forAll genG2element
      G2.add p1 (G2.add p2 p3) === G2.add (G2.add p1 p2) p3

prop_G2_assoc_plutus :: TestTree
prop_G2_assoc_plutus =
    testPropertyNamed
    "Addition in G2 is associative"
    "G2_assoc_plutus" .
    withNTests $ property $ do
      p1 <- forAll genG2element
      p2 <- forAll genG2element
      p3 <- forAll genG2element
      let e1 = addG2 (g2elt p1) (addG2 (g2elt p2) (g2elt p3))
          e2 = addG2 (addG2 (g2elt p1) (g2elt p2)) (g2elt p3)
          e3 = eqG2 e1 e2
      evalTerm e3 === uplcTrue

prop_G2_abelian :: TestTree
prop_G2_abelian =
    testPropertyNamed
    "Addition in G2 is commutative"
    "G2_abelian" .
    withNTests $ property $ do
      p1 <- forAll genG2element
      p2 <- forAll genG2element
      G2.add p1 p2 === G2.add p2 p1

prop_G2_abelian_plutus :: TestTree
prop_G2_abelian_plutus =
    testPropertyNamed
    "Addition in G2 is commutative"
    "G2_abelian_plutus" .
    withNTests $ property $ do
      p1 <- forAll genG2element
      p2 <- forAll genG2element
      let e1 = addG2 (g2elt p1) (g2elt p2)
          e2 = addG2 (g2elt p2) (g2elt p1)
          e3 = eqG2 e1 e2
      evalTerm e3 === uplcTrue

prop_G2_mul :: TestTree
prop_G2_mul =
    testPropertyNamed
    "Scalar multiplication is repeated addition in G2"
    "G2_scalar_multiplication" .
    withNTests $ property $ do
      n <- forAll genScalar
      p <- forAll genG2element
      G2.mul n p === repeatedAddG2 n p

{-
prop_G2_mul_plutus :: TestTree_plutus
prop_G2_mul_plutus =
    testPropertyNamed
    "Scalar multiplication is repeated addition in G2"
    "G2_scalar_multiplication" .
    withNTests $ property $ do
      n <- forAll genScalar
      p <- forAll genG2element
      G2.mul n p === repeatedAddG2 n p
-}

prop_G2_zero :: TestTree
prop_G2_zero =
    testPropertyNamed
    "The point at infinity is an additive identity in G2"
    "G2_zero" .
    withNTests $ property $ do
      p <- forAll genG2element
      p === G2.add p G2.zero

prop_G2_zero_plutus :: TestTree
prop_G2_zero_plutus =
    testPropertyNamed
    "The point at infinity is an additive identity in G2"
    "G2_zero_plutus" .
    withNTests $ property $ do
      p <- forAll genG2element
      let e1 = addG2 (g2elt p) zeroG2
          e2 = eqG2 (g2elt p) e1
      evalTerm e2 === uplcTrue

prop_G2_neg :: TestTree
prop_G2_neg =
    testPropertyNamed
    "Every point in G2 has an additive inverse"
    "G2_inverse" .
    withNTests $ property $ do
      p <- forAll genG2element
      G2.add p (G2.neg p) === G2.zero

prop_G2_neg_plutus :: TestTree
prop_G2_neg_plutus =
    testPropertyNamed
    "Every point in G2 has an additive inverse"
    "G2_inverse_plutus" .
    withNTests $ property $ do
      p <- forAll genG2element
      let e1 = addG2 (g2elt p) (negG2 (g2elt p))
          e2 = eqG2 e1 zeroG2
      evalTerm e2 === uplcTrue

prop_G2_scalar_inverse :: TestTree
prop_G2_scalar_inverse =
    testPropertyNamed
    "-p = (-1)*p for all p in G2"
    "G2_scalar_inverse" .
    withNTests $ property $ do
      p <- forAll genG2element
      G2.neg p === G2.mul (-1) p

prop_G2_scalar_inverse_plutus :: TestTree
prop_G2_scalar_inverse_plutus =
    testPropertyNamed
    "-p = (-1)*p for all p in G2"
    "G2_scalar_inverse_plutus" .
    withNTests $ property $ do
      p <- forAll genG2element
      let e1 = negG2 (g2elt p)
          e2 = mulG2 (integer (-1)) (g2elt p)
          e3 = eqG2 e1 e2
      evalTerm e3 === uplcTrue

prop_G2_scalar_identity :: TestTree
prop_G2_scalar_identity =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G2"
    "G2_scalar_identity" .
    withNTests $ property $ do
      p <- forAll genG2element
      G2.mul 1 p === p

prop_G2_scalar_identity_plutus :: TestTree
prop_G2_scalar_identity_plutus =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G2"
    "G2_scalar_identity_plutus" .
    withNTests $ property $ do
      p <- forAll genG2element
      let e = eqG2 (mulG2 (integer 1) (g2elt p)) (g2elt p)
      evalTerm e === uplcTrue

prop_G2_scalar_zero :: TestTree
prop_G2_scalar_zero =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G2"
    "G2_scalar_zero" .
    withNTests $ property $ do
      p <- forAll genG2element
      G2.mul 0 p === G2.zero

prop_G2_scalar_zero_plutus :: TestTree
prop_G2_scalar_zero_plutus =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G2"
    "G2_scalar_zero_plutus" .
    withNTests $ property $ do
      p <- forAll genG2element
      let e1 = mulG2 (integer 0) (g2elt p)
          e2 = eqG2 e1 zeroG2
      evalTerm e2 === uplcTrue

prop_G2_scalar_assoc :: TestTree
prop_G2_scalar_assoc =
    testPropertyNamed
    "Scalar multiplication is associative in G2"
    "G2_scalar_assoc" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG2element
      G2.mul a (G2.mul b p) === G2.mul (a*b) p

prop_G2_scalar_assoc_plutus :: TestTree
prop_G2_scalar_assoc_plutus =
    testPropertyNamed
    "Scalar multiplication is associative in G2"
    "G2_scalar_assoc_plutus" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG2element
      let e1 = mulG2 (mkApp2 (builtin () MultiplyInteger) (integer a) (integer b)) (g2elt p)
          e2 = mulG2 (integer a) (mulG2 (integer b) (g2elt p))
          e3 = eqG2 e1 e2
      evalTerm e3 === uplcTrue

prop_G2_scalar_distributive :: TestTree
prop_G2_scalar_distributive =
    testPropertyNamed
    "Scalar multiplication distributes over addition in G2"
    "G2_scalar_distributive" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG2element
      G2.mul (a+b) p === G2.add (G2.mul a p) (G2.mul b p)

prop_G2_scalar_distributive_plutus :: TestTree
prop_G2_scalar_distributive_plutus =
    testPropertyNamed
    "Scalar multiplication distributes over addition in G2"
    "G2_scalar_distributive_plutus" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG2element
      let e1 = mulG2 (mkApp2 (builtin () AddInteger) (integer a) (integer b)) (g2elt p)
          e2 = addG2 (mulG2 (integer a) (g2elt p))  (mulG2 (integer b) (g2elt p))
          e3 = eqG2 e1 e2
      evalTerm e3 === uplcTrue

prop_G2_compression :: TestTree
prop_G2_compression =
    testPropertyNamed
    "Compression followed by unconpression is the identity function on G2"
    "G2_compression_distributive" .
    withNTests $ property $ do
      p <- forAll genG2element
      case G2.uncompress (G2.compress p) of
        Left e  -> error $ show e
        Right q -> p === q

prop_G2_compression_plutus :: TestTree
prop_G2_compression_plutus =
    testPropertyNamed
    "Compression followed by uncompression is the identity function on G2"
    "G2_compression_distributive_plutus" .
    withNTests $ property $ do
      p <- forAll genG2element
      let e1 = uncompressG2 (compressG2 (g2elt p))
          e2 = eqG2 e1 (g2elt p)
      evalTerm e2 === uplcTrue

prop_G2_hash :: TestTree
prop_G2_hash =
    testPropertyNamed
    "Different inputs hash to different points in G2"
    "G2_no_hash_collisions" .
    withNTests $ property $ do
      b1 <- forAll genByteString
      b2 <- forAll genByteString
      when (b1 /= b2) $
           G2.hashToCurve b1 /== G2.hashToCurve b2

prop_G2_hash_plutus :: TestTree
prop_G2_hash_plutus =
    testPropertyNamed
    "Different inputs hash to different points in G2"
    "G2_no_hash_collisions_plutus" .
    withNTests $ property $ do
      b1 <- forAll genByteString
      b2 <- forAll genByteString
      when (b1 /= b2) $ do
           let e = eqG2 (hashToCurveG2 (bytestring b1)) (hashToCurveG2 (bytestring b2))
           evalTerm e === uplcFalse

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

test_G2_plutus :: TestTree
test_G2_plutus =
    testGroup "G2"
        [ prop_G2_assoc_plutus
        , prop_G2_abelian_plutus
        , prop_G2_zero_plutus
        , prop_G2_neg_plutus
        , prop_G2_scalar_zero_plutus
        , prop_G2_scalar_inverse_plutus
        , prop_G2_scalar_assoc_plutus
        , prop_G2_scalar_distributive_plutus
        , prop_G2_scalar_identity_plutus
        --, prop_G2_mul_plutus
        , prop_G2_compression_plutus
        , prop_G2_hash_plutus
        ]

---------------- Pairing tests ----------------

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
    withNTests $ property $ do
      p1 <- forAll genG1element
      p2 <- forAll genG1element
      q <- forAll genG2element
      GT.finalVerify (pairing (G1.add p1 p2) q) (GT.mul (pairing p1 q) (pairing p2 q)) === True

-- <p1+p2,q> = <p1,q>.<p2,q>
prop_pairing_left_additive_plutus :: TestTree
prop_pairing_left_additive_plutus =
    testPropertyNamed
    "Pairing is left additive"
    "pairing_left_additive_plutus" .
    withNTests $ property $ do
      p1_ <- forAll genG1element
      p2_ <- forAll genG1element
      q_ <- forAll genG2element
      let p1 = g1elt p1_
          p2 = g1elt p2_
          q  = g2elt q_
          e1 = pairingPlc (addG1 p1 p2) q
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
      p <- forAll genG1element
      q1 <- forAll genG2element
      q2 <- forAll genG2element
      GT.finalVerify (pairing p (G2.add q1 q2)) (GT.mul (pairing p q1) (pairing p q2)) === True

-- <p,q1+q2> = <p,q1>.<p,q2>
prop_pairing_right_additive_plutus :: TestTree
prop_pairing_right_additive_plutus =
    testPropertyNamed
    "Pairing is right additive"
    "pairing_right_additive_plutus" .
    withNTests $ property $ do
      p_ <- forAll genG1element
      q1_ <- forAll genG2element
      q2_ <- forAll genG2element
      let p  = g1elt p_
          q1 = g2elt q1_
          q2 = g2elt q2_
          e1 = pairingPlc p (addG2 q1 q2)
          e2 = mulGT (pairingPlc p q1) (pairingPlc p q2)
          e3 = finalVerifyPlc e1 e2
      evalTerm e3 === uplcTrue

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

-- <ap, q> == <p,aq> for all a in Z, p in G1, q in G2
prop_pairing_balanced_plutus :: TestTree
prop_pairing_balanced_plutus =
    testPropertyNamed
    "Pairing is balanced"
    "pairing_balanced" .
    withNTests $ property $ do
      a_ <- forAll genScalar
      p_ <- forAll genG1element
      q_ <- forAll genG2element
      let a = integer a_
          p = g1elt p_
          q = g2elt q_
          e1 = pairingPlc (mulG1 a p) q
          e2 = pairingPlc p (mulG2 a q)
          e3 = finalVerifyPlc e1 e2
      evalTerm e3 === uplcTrue

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
       let x = case GT.millerLoop a b of
                 Left e   -> error $ show e
                 Right xx -> xx
       let y = case GT.millerLoop a' b' of
                 Left e   -> error $ show e
                 Right yy -> yy
       when (a /= a' || b /= b') $ (GT.finalVerify x y === False)


-- ???? Why can millerLoop fail ????? --
-- Because it's checking that its arguments are in the correct groups.

prop_random_pairing_plutus :: TestTree
prop_random_pairing_plutus =
    testPropertyNamed
    "Pairings of random points are unequal"
    "pairing_random_plutus" .
    withNTests $ property $ do
       p1_ <- forAll genG1element
       q1_ <- forAll genG2element
       p2_ <- forAll genG1element
       q2_ <- forAll genG2element
       when (p1_ /= p2_ || q1_  /= q2_) $
            let p1 = g1elt p1_
                q1 = g2elt q1_
                p2 = g1elt p2_
                q2 = g2elt q2_
                e = finalVerifyPlc (pairingPlc p1 q1) (pairingPlc p2 q2)
            in evalTerm e === uplcFalse

test_pairing :: TestTree
test_pairing =
    testGroup "Pairing"
        [ prop_pairing_left_additive
        , prop_pairing_right_additive
        , prop_pairing_balanced
        , prop_random_pairing
        ]

test_pairing_plutus :: TestTree
test_pairing_plutus =
    testGroup "Pairing"
        [ prop_pairing_left_additive_plutus
        , prop_pairing_right_additive_plutus
        , prop_pairing_balanced_plutus
        , prop_random_pairing_plutus
        ]

test_plutus :: TestTree
test_plutus =
    testGroup "BLS12-381 (Plutus)"
    [ test_G1_plutus
    , test_G2_plutus
    , test_pairing_plutus
    ]


test_haskell :: TestTree
test_haskell =
    testGroup "BLS12-381 (Haskell)"
    [ test_G1
    , test_G2
    , test_pairing
    ]


test_BLS12_381 :: TestTree
test_BLS12_381 =
    testGroup "BLS12-381"
    [ test_haskell
    , test_plutus
    ]
