{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}

module Evaluation.Builtins.BLS12_381.PlutusTests (tests)
where

import Evaluation.Builtins.BLS12_381.Common
import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2
import PlutusCore.Default

import Control.Monad (liftM, when)
import Crypto.EllipticCurve.BLS12_381 (BLSTError)
import Data.ByteString as BS (length)
import Data.List (foldl', genericReplicate)
import Data.String (fromString)
import Text.Printf (printf)

import Hedgehog hiding (Group (..))
import Hedgehog.Gen qualified as Gen

import Test.Tasty
import Test.Tasty.Hedgehog


forAllElements :: forall a m . (TestableAbelianGroup a, Monad m) => PropertyT m PlcTerm
forAllElements = liftM toPlc <$> forAll $ genElement @a

forAllG1 :: forall m . Monad m => PropertyT m PlcTerm
forAllG1 =  forAllElements @G1.Element

forAllG2 :: forall m . Monad m => PropertyT m PlcTerm
forAllG2 =  forAllElements @G2.Element

---------------- G is an Abelian group ----------------

prop_assoc :: forall a. TestableAbelianGroup a => TestTree
prop_assoc =
    testPropertyNamed
    (printf "Addition in %s is associative" name)
    (fromString $ printf "%s_assoc" name) .
    withNTests $ property $ do
      p1 <- liftM toPlc <$> forAll $ genElement @a
      p2 <- forAllElements @a
      p3 <- forAllElements @a
      let e = eqP @a (addP @a p1 (addP @a p2 p3)) (addP @a (addP @a p1 p2) p3)
      evalTerm e === uplcTrue
        where name = gname @a

prop_zero :: forall a. TestableAbelianGroup a => TestTree
prop_zero =
    testPropertyNamed
    (printf "The zero element is the additive identity in %s" name)
    (fromString $ printf "%s_zero" name) .
    withNTests $ property $ do
      p <- forAllElements @a
      let e = eqP @a (addP @a  p $ zeroP @a) p
      evalTerm e === uplcTrue
        where name = gname @a

prop_neg :: forall a. TestableAbelianGroup a => TestTree
prop_neg =
    testPropertyNamed
    (printf "Every point in %s has an additive inverse" name)
    (fromString $ printf "%s_inverse" name) .
    withNTests $ property $ do
      p <- forAllElements @a
      let e = eqP @a (addP @a p (negP @a p)) $ zeroP @a
      evalTerm e === uplcTrue
        where name = gname @a

prop_abelian :: forall a. TestableAbelianGroup a => TestTree
prop_abelian =
    testPropertyNamed
    (printf "Addition in %s is commutative" name)
    (fromString $ printf "%s_abelian" name) .
    withNTests $ property $ do
      p1 <- forAllElements @a
      p2 <- forAllElements @a
      let e = eqP @a (addP @a p1 p2) (addP @a p2 p1)
      evalTerm e === uplcTrue
        where name = gname @a

test_is_an_Abelian_group :: forall a. TestableAbelianGroup a => TestTree
test_is_an_Abelian_group =
    testGroup "G1 is an Abelian group"
         [ prop_assoc   @a
         , prop_zero    @a
         , prop_neg     @a
         , prop_abelian @a
         ]

---------------- Z acts on G correctly ----------------

prop_scalar_assoc :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_assoc =
    testPropertyNamed
    (printf "Scalar multiplication is associative in %s" name)
    (fromString $ printf "%s_scalar_assoc" name) .
    withNTests $ property $ do
      a <- integer <$> forAll genScalar
      b <- integer <$> forAll genScalar
      p <- forAllElements @a
      let e1 = mulP @a (mkApp2 MultiplyInteger a b) p
          e2 = mulP @a a (mulP @a b p)
          e3 = eqP @a e1 e2
      evalTerm e3 === uplcTrue
        where name = gname @a

prop_scalar_zero :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_zero =
    testPropertyNamed
    (printf "Scalar multiplication by 0 always yields the zero element of %s" name)
    (fromString $ printf "%s_scalar_zero" name) .
    withNTests $ property $ do
      p <- forAllElements @a
      let e = eqP @a (mulP @a (integer 0) p) $ zeroP @a
      evalTerm e === uplcTrue
          where name = gname @a

prop_scalar_identity :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_identity =
    testPropertyNamed
    (printf "Scalar multiplication by 1 is the identity function on %s" name)
    (fromString $ printf "%s_scalar_identity" name) .
    withNTests $ property $ do
      p <- forAllElements @a
      let e = eqP @a (mulP @a (integer 1) p) p
      evalTerm e === uplcTrue
        where name = gname @a

prop_scalar_inverse :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_inverse =
    testPropertyNamed
    (printf "-p = (-1)*p for all p in %s" name)
    (fromString $ printf "%s_scalar_inverse" $ gname @a) .
    withNTests $ property $ do
      p <- forAll $ genElement @a
      neg p === mul (-1) p
        where name = gname @a

prop_scalar_distributive :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_distributive =
    testPropertyNamed
    (printf "Scalar multiplication distributes over addition in %s" name)
    (fromString $ printf "%s_scalar_distributive" name) .
    withNTests $ property $ do
      a <- integer <$> forAll genScalar
      b <- integer <$> forAll genScalar
      p <- forAllElements @a
      let e1 = mulP @a (mkApp2 AddInteger a b) p
          e2 = addP @a (mulP @a a p) (mulP @a b p)
          e3 = eqP @a e1 e2
      evalTerm e3 === uplcTrue
        where name = gname @a

prop_scalar_multiplication :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_multiplication =
    let name = gname @a in
    testPropertyNamed
    (printf "Scalar multiplication is repeated addition in %s" name)
    (fromString $ printf "%s_scalar_multiplication" name) .
    withNTests $ property $ do
      n <- forAll genSmallScalar
      p <- forAllElements @a
      let e1 = repeatedAdd n p
          e2 = eqP @a (mulP @a (integer n) p) e1
      evalTerm e2 === uplcTrue
          where
            repeatedAdd :: Integer -> PlcTerm -> PlcTerm
            repeatedAdd n t =
                if n>=0
                then foldl' (addP @a) (zeroP @a) $ genericReplicate n t
                else repeatedAdd (-n) (negP @a t)

test_Z_action_good :: forall a. TestableAbelianGroup a => TestTree
test_Z_action_good =
    testGroup (printf "Z acts correctly on %s" name)
         [ prop_scalar_zero           @a
         , prop_scalar_inverse        @a
         , prop_scalar_assoc          @a
         , prop_scalar_distributive   @a
         , prop_scalar_identity       @a
         , prop_scalar_multiplication @a
         ]
        where name = gname @a


---------------- Compression, uncompression, and hashing work properly ----------------

prop_roundtrip_compression :: forall e a. HashAndCompress e a => TestTree
prop_roundtrip_compression =
    testPropertyNamed
    (printf "Compression followed by uncompression is the identity function on %s" name)
    (fromString $ printf "%s_roundtrip_compression" name) .
    withNTests $
    withShrinks 0 $
    property $ do
      p <- forAllElements @a
      let e = eqP @a (uncompressP @e @a (compressP @e @a p)) p
      evalTerm e === uplcTrue
        where name = gname @a

-- Uncompression should only accept inputs of length (but not all inputs of
-- length are valid).

-- There's no point in shrinking here; in fact, if you use `filter` on the
-- generator, Hedgehog occasionally seems to go into an infinite loop if you
-- deliberately let good inputs through (eg, by putting the wrong size in the
-- filter).
prop_uncompression_input_size :: forall e a. HashAndCompress e a => TestTree
prop_uncompression_input_size =
    testPropertyNamed
    (printf "%s uncompression fails if the input has length not equal to %d" name expectedSize)
    (fromString $ printf "%s_uncompression_input_size" name) .
    withTests 1000 $
    withShrinks 0 $
    property $ do
      b <- bytestring <$> (forAll $ Gen.filter (\x -> BS.length x /= expectedSize) genByteString100)
      let e = uncompressP @e @a b
      evalTerm e === Nothing
        where expectedSize = fromIntegral $ compressedSize @e @a
              name = gname @a

prop_hash :: forall e a. HashAndCompress e a => TestTree
prop_hash =
    testPropertyNamed
    (printf "Different inputs hash to different points in %s" name)
    (fromString $ printf "%s_no_hash_collisions" name) .
    withNTests $
    withShrinks 0 $
    withNTests $ property $ do
      b1 <- forAll genByteString
      b2 <- forAll $ Gen.filter (/= b1) genByteString
      let e = eqP @a (hashToCurveP @e @a $ bytestring b1) (hashToCurveP @e @a $ bytestring b2)
      evalTerm e === uplcFalse
        where name = gname @a

test_compress_hash :: forall e a. HashAndCompress e a => TestTree
test_compress_hash =
    testGroup (printf "Uncompression and hashing behave properly for %s" $ gname @a)
         [ prop_roundtrip_compression @e @a
         , prop_uncompression_input_size @e @a
         , prop_hash @e @a
         ]

---------------- Pairing properties

-- <p1+p2,q> = <p1,q>.<p2,q>
prop_pairing_left_additive :: TestTree
prop_pairing_left_additive =
    testPropertyNamed
    "Pairing is left additive"
    "pairing_left_additive" .
    withNTests $ property $ do
      p1 <- forAllG1
      p2 <- forAllG1
      q  <- forAllG2
      let e1 = pairingPlc (addP @G1.Element p1 p2) q
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
      p  <- forAllG1
      q1 <- forAllG2
      q2 <- forAllG2
      let e1 = pairingPlc p (addP @G2.Element q1 q2)
          e2 = mulGT (pairingPlc p q1) (pairingPlc p q2)
          e3 = finalVerifyPlc e1 e2
      evalTerm e3 === uplcTrue

-- <[n]p,q> = <p,[n]q>
prop_pairing_balanced :: TestTree
prop_pairing_balanced =
    testPropertyNamed
    "Pairing is balanced"
    "pairing_balanced" .
    withNTests $ property $ do
      n <- integer <$> forAll genScalar
      p <- forAllG1
      q <- forAllG2
      let e1 = pairingPlc (mulP @G1.Element n p) q
          e2 = pairingPlc p (mulP @G2.Element n q)
          e3 = finalVerifyPlc e1 e2
      evalTerm e3 === uplcTrue

prop_random_pairing :: TestTree
prop_random_pairing =
    testPropertyNamed
    "Pairings of random points are unequal"
    "pairing_random" .
    withNTests $ property $ do
       p1 <- forAllG1
       p2 <- forAllG1
       q1 <- forAllG2
       q2 <- forAllG2
       when (p1 /= p2 && q1 /= q2) $
            -- || or &&? Surely <0,q> = 1 for all q, so we could get a collision here
            do
              let e = finalVerifyPlc (pairingPlc p1 q1) (pairingPlc p2 q2)
              evalTerm e === uplcFalse

-- All the tests

tests :: TestTree
tests = testGroup "*** Plutus property tests ***" [
         testGroup "G1 properties"
         [ test_is_an_Abelian_group @G1.Element
         , test_Z_action_good       @G1.Element
         , test_compress_hash       @BLSTError @G1.Element
         ]
        , testGroup "G2 properties"
         [ test_is_an_Abelian_group @G2.Element
         , test_Z_action_good       @G2.Element
         , test_compress_hash       @BLSTError @G2.Element
         ]
        , testGroup "Pairing properties"
         [ prop_pairing_left_additive
         , prop_pairing_right_additive
         , prop_pairing_balanced
         , prop_random_pairing
         ]
        ]

