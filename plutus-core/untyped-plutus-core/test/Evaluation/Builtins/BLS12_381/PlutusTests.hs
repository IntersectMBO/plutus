{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}

module Evaluation.Builtins.BLS12_381.PlutusTests (tests)
where

import Crypto.BLS12_381.G1 qualified as G1
import Crypto.BLS12_381.G2 qualified as G2
import Evaluation.Builtins.BLS12_381.Common
import PlutusCore.Default

import Crypto.External.EllipticCurve.BLS12_381 (scalarPeriod)
import Data.ByteString as BS (length)
import Data.List (foldl', genericReplicate)
import Text.Printf (printf)

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

-- QuickCheck generators for scalars and group elements as PLC terms

arbitraryConstant :: forall a . TestableAbelianGroup a => Gen PlcTerm
arbitraryConstant = toPlc <$> (arbitrary @a)

arbitraryScalar :: Gen PlcTerm
arbitraryScalar = integer <$> (arbitrary @Integer)

---------------- G is an Abelian group ----------------

-- | Group addition is associative.
test_add_assoc :: forall a. TestableAbelianGroup a => TestTree
test_add_assoc =
    testProperty
    (mkTestName @a "add_assoc") .
    withNTests $ do
      p1 <- arbitraryConstant @a
      p2 <- arbitraryConstant @a
      p3 <- arbitraryConstant @a
      let e = eqP @a (addP @a p1 (addP @a p2 p3)) (addP @a (addP @a p1 p2) p3)
      pure $ evalTerm e === uplcTrue

-- | Zero is an identity for addition.
test_add_zero :: forall a. TestableAbelianGroup a => TestTree
test_add_zero =
    testProperty
    (mkTestName @a "add_zero") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (addP @a  p $ zeroP @a) p
      pure $ evalTerm e === uplcTrue

-- | Every element has an inverse
-- | a+(-a) = 0 for all group elements.
test_neg :: forall a. TestableAbelianGroup a => TestTree
test_neg =
    testProperty
    (mkTestName @a "additive_inverse") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (addP @a p (negP @a p)) $ zeroP @a
      pure $ evalTerm e === uplcTrue

-- | Group addition is commutative.
test_add_commutative :: forall a. TestableAbelianGroup a => TestTree
test_add_commutative=
    testProperty
    (mkTestName @a "add_commutative") .
    withNTests $ do
      p1 <- arbitraryConstant @a
      p2 <- arbitraryConstant @a
      let e = eqP @a (addP @a p1 p2) (addP @a p2 p1)
      pure $ evalTerm e === uplcTrue

test_is_an_abelian_group :: forall a. TestableAbelianGroup a => TestTree
test_is_an_abelian_group =
    testGroup (mkTestName @a "is_an_abelian_group")
              [ test_add_assoc       @a
              , test_add_zero        @a
              , test_neg             @a
              , test_add_commutative @a
              ]


---------------- Z acts on G correctly ----------------

-- | (ab)p = a(bp) for all scalars a and b and all group elements p.
test_scalarMul_assoc :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_assoc =
    testProperty
    (mkTestName @a "scalarMul_mul_assoc") .
    withNTests $ do
      m <- arbitraryScalar
      n <- arbitraryScalar
      p <- arbitraryConstant @a
      let e1 = scalarMulP @a (mkApp2 MultiplyInteger m n) p
          e2 = scalarMulP @a m (scalarMulP @a n p)
          e3 = eqP @a e1 e2
      pure $ evalTerm e3 === uplcTrue

-- | (a+b)p = ap +bp for all scalars a and b and all group elements p.
test_scalarMul_distributive_left :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_distributive_left =
    testProperty
    (mkTestName @a "scalarMul_distributive_left") .
    withNTests $  do
      m <- arbitraryScalar
      n <- arbitraryScalar
      p <- arbitraryConstant @a
      let e1 = scalarMulP @a (mkApp2 AddInteger m n) p
          e2 = addP @a (scalarMulP @a m p) (scalarMulP @a n p)
          e3 = eqP @a e1 e2
      pure $ evalTerm e3 === uplcTrue

-- | a(p+q) = ap + aq for all scalars a and all group elements p and q.
test_scalarMul_distributive_right :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_distributive_right =
    testProperty
    (mkTestName @a "scalarMul_distributive_right") .
    withNTests $  do
      n <- arbitraryScalar
      p <- arbitraryConstant @a
      q <- arbitraryConstant @a
      let e1 = scalarMulP @a n (addP @a p q)
          e2 = addP @a (scalarMulP @a n p) (scalarMulP @a n q)
          e3 = eqP @a e1 e2
      pure $ evalTerm e3 === uplcTrue

-- | 0p = 0 for all group elements p.
test_scalarMul_zero :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_zero =
    testProperty
    (mkTestName @a "scalarMul_zero") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (scalarMulP @a (integer 0) p) $ zeroP @a
      pure $ evalTerm e === uplcTrue

-- | 1p = p for all group elements p.
test_scalarMul_one :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_one =
    testProperty
    (mkTestName @a "scalarMul_one") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (scalarMulP @a (integer 1) p) p
      pure $ evalTerm e === uplcTrue

-- | (-1)p = -p for all group elements p.
test_scalarMul_inverse :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_inverse =
    testProperty
    (mkTestName @a "scalarMul_inverse") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (scalarMulP @a (integer (-1)) p) (negP @a p)
      pure $ evalTerm e == uplcTrue

-- Check that scalar multiplication is repeated addition (including negative
-- scalars). We should really check this for scalars greater than the group
-- order, but that would be prohibitively slow because the order of G1 and G2
-- has 256 bits (about 5*10^76).
test_scalarMul_repeated_addition :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_repeated_addition =
    testProperty
    (mkTestName @a "scalarMul_repeated_addition") .
    withNTests $ do
      n <- resize 100 arbitrary
      p <- arbitraryConstant @a
      let e1 = repeatedAdd n p
          e2 = eqP @a (scalarMulP @a (integer n) p) e1
      pure $ evalTerm e2 === uplcTrue
          where
            repeatedAdd :: Integer -> PlcTerm -> PlcTerm
            repeatedAdd n t =
                if n>=0
                then foldl' (addP @a) (zeroP @a) $ genericReplicate n t
                else repeatedAdd (-n) (negP @a t)

-- (m + n|G|)p = mp for all group elements p and integers m and n.
-- We have |G1| = |G2| = scalarPeriod
test_scalarMul_periodic :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_periodic =
    testProperty
    (mkTestName @a "scalarMul_periodic") .
    withNTests $ do
      m <- arbitraryScalar
      n <- arbitraryScalar
      p <- arbitraryConstant @a
      let e1 = scalarMulP @a m p
          k = mkApp2 AddInteger m (mkApp2 MultiplyInteger n (integer scalarPeriod))
          e2 = scalarMulP @a k p -- k = m+n|G|
          e = eqP @a e1 e2
      pure $ evalTerm e === uplcTrue

test_Z_action_good :: forall a. TestableAbelianGroup a => TestTree
test_Z_action_good =
    testGroup (printf "Z acts correctly on %s" $ gname @a)
         [ test_scalarMul_assoc              @a
         , test_scalarMul_distributive_left  @a
         , test_scalarMul_distributive_right @a
         , test_scalarMul_zero               @a
         , test_scalarMul_one                @a
         , test_scalarMul_inverse            @a
         , test_scalarMul_repeated_addition  @a
         , test_scalarMul_periodic           @a
         ]


---------------- Compression, uncompression, and hashing work properly ----------------

test_roundtrip_compression :: forall a. HashAndCompress a => TestTree
test_roundtrip_compression =
    testProperty
    (mkTestName @a "roundtrip_compression") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (uncompressP @a (compressP @a p)) p
      pure $ evalTerm e === uplcTrue

-- | Uncompression should only accept inputs of the expected length, so we check
-- it on random inputs of the incorrect length.  Inputs of the expected length
-- are excluded by the incorrectSize predicate; however even if an input did
-- have the expected length it would be very unlikely to deserialise to a point
-- in the group because the cofactors are very big (7.6*10^37 for G1 and
-- 3.1*10^152 for G2).
test_uncompression_wrong_size :: forall a . HashAndCompress a => TestTree
test_uncompression_wrong_size =
    testProperty
    (mkTestName @a "uncompression_wron_size") .
    withNTests $ do
      b <- suchThat (resize 128 arbitrary) incorrectSize
      let e = uncompressP @a (bytestring b)
      pure $ evalTerm e === CekError
    where incorrectSize s = BS.length s /= compressedSize @a

-- | This tests the case we've omitted in the previous test, and should fail
-- with very high probablity.  It's quite difficult to test this with random
-- inputs.  We can improve our chances of getting a bytestring which encodes a
-- point on the curve by setting the compression bit and clearing the infinity
-- bit, but about 50% of the samples will still not be the x-coordinate of a
-- point on the curve.  We can generate also generate points with an
-- x-coordinate that's bigger than the field size (especially for G2), which
-- will give us a bad encoding.  Maybe this just isn't a very good test.
test_uncompress_out_of_group :: forall a . HashAndCompress a => TestTree
test_uncompress_out_of_group =
    testProperty
    (mkTestName @a "uncompress_out_of_group") .
    withMaxSuccess 400 $ do
      b <- suchThat (resize  128 arbitrary) correctSize
      let b' = setBits compressionBit $ clearBits infinityBit b
      let e = uncompressP @a (bytestring b')
      pure $ evalTerm e === CekError
    where correctSize s = BS.length s == compressedSize @a

-- | Check that the most significant bit is set for all compressed points
test_compression_bit_set :: forall a. HashAndCompress a => TestTree
test_compression_bit_set =
    testProperty
    (mkTestName @a "compression_bit_set") .
    withNTests $ do True === True

-- | Check that bytestrings with the compression bit clear fail to uncompress.
test_clear_compression_bit :: forall a. HashAndCompress a => TestTree
test_clear_compression_bit =
    testProperty
    (mkTestName @a "clear_compression_bit") .
    withNTests $ do
      p <- arbitrary @a
      let b = clearBits compressionBit $ compress @a p
          e = uncompressP @a (bytestring b)
      pure $ evalTerm e === CekError

-- | Check that flipping the sign bit in a compressed point gives the inverse of
-- the point.
test_flip_sign_bit :: forall a. HashAndCompress a => TestTree
test_flip_sign_bit =
    testProperty
    (mkTestName @a "flip_sign_bit") .
    withNTests $ do
      p <- arbitrary @a
      let b1 = compress @a p
          b2 = flipBits signBit b1
          e1 = uncompressP @a (bytestring b1)
          e2 = uncompressP @a (bytestring b2)
          e  = eqP @a e2 (negP @a e1)
      pure $ evalTerm e === uplcTrue

-- | Check that bytestrings with the infinity bit set fail to uncompress.
test_set_infinity_bit :: forall a. HashAndCompress a => TestTree
test_set_infinity_bit =
    testProperty
    (mkTestName @a "set_infinity_bit") .
    withNTests $ do
      p <- arbitrary @a
      let b = setBits infinityBit $ compress @a p
          e = uncompressP @a (bytestring b)
      pure $ evalTerm e === CekError

-- | Hashing into G1 or G2 should be collision-free. A failure here would be
-- interesting.
test_no_hash_collisions :: forall a . HashAndCompress a => TestTree
test_no_hash_collisions =
    testProperty
    (mkTestName @a "no_hash_collisions") .
    withNTests $ do
      b1 <- arbitrary
      b2 <- arbitrary
      let e = eqP @a (hashToGroupP @a $ bytestring b1) (hashToGroupP @a $ bytestring b2)
      pure $ b1 /= b2 ==> evalTerm e === uplcFalse

test_compress_hash :: forall a. HashAndCompress a => TestTree
test_compress_hash =
    testGroup (printf "Uncompression and hashing behave properly for %s" $ gname @a)
         [ test_roundtrip_compression    @a
         , test_uncompression_wrong_size @a
         , test_compression_bit_set      @a
         , test_clear_compression_bit    @a
         , test_flip_sign_bit            @a
         , test_set_infinity_bit         @a
         , test_uncompress_out_of_group  @a
         , test_no_hash_collisions       @a
         ]


---------------- Pairing properties ----------------

-- <p1+p2,q> = <p1,q>.<p2,q>
test_pairing_left_additive :: TestTree
test_pairing_left_additive =
    testProperty
    "pairing_left_additive" .
    withNTests $ do
      p1 <- arbitraryConstant @G1.Element
      p2 <- arbitraryConstant @G1.Element
      q  <- arbitraryConstant @G2.Element
      let e1 = millerLoopPlc (addP @G1.Element p1 p2) q
          e2 = mulMlResultPlc (millerLoopPlc p1 q) (millerLoopPlc p2 q)
          e3 = finalVerifyPlc e1 e2
      pure $ evalTerm e3 === uplcTrue

-- <p,q1+q2> = <p,q1>.<p,q2>
test_pairing_right_additive :: TestTree
test_pairing_right_additive =
    testProperty
    "pairing_right_additive" .
    withNTests $ do
      p  <- arbitraryConstant @G1.Element
      q1 <- arbitraryConstant @G2.Element
      q2 <- arbitraryConstant @G2.Element
      let e1 = millerLoopPlc p (addP @G2.Element q1 q2)
          e2 = mulMlResultPlc (millerLoopPlc p q1) (millerLoopPlc p q2)
          e3 = finalVerifyPlc e1 e2
      pure $ evalTerm e3 === uplcTrue

-- <[n]p,q> = <p,[n]q>
test_pairing_balanced :: TestTree
test_pairing_balanced =
     testProperty
     "pairing_balanced" .
     withNTests $ do
      n <- arbitraryScalar
      p <- arbitraryConstant @G1.Element
      q <- arbitraryConstant @G2.Element
      let e1 = millerLoopPlc (scalarMulP @G1.Element n p) q
          e2 = millerLoopPlc p (scalarMulP @G2.Element n q)
          e3 = finalVerifyPlc e1 e2
      pure $ evalTerm e3 === uplcTrue

-- finalVerify returns False for random inputs
test_random_pairing :: TestTree
test_random_pairing =
    testProperty
    "pairing_random_unequal" .
    withNTests $ do
       p1 <- arbitraryConstant @G1.Element
       p2 <- arbitraryConstant @G1.Element
       q1 <- arbitraryConstant @G2.Element
       q2 <- arbitraryConstant @G2.Element
       pure $ p1 /= p2 && q1 /= q2 ==>
            let e = finalVerifyPlc (millerLoopPlc p1 q1) (millerLoopPlc p2 q2)
            in evalTerm e === uplcFalse


-- All the tests

tests :: TestTree
tests = testGroup "*** Plutus property tests ***" [
         testGroup "G1 properties"
         [ test_is_an_abelian_group @G1.Element
         , test_Z_action_good       @G1.Element
         , test_compress_hash       @G1.Element
         ]
        , testGroup "G2 properties"
         [ test_is_an_abelian_group @G2.Element
         , test_Z_action_good       @G2.Element
         , test_compress_hash       @G2.Element
         ]
        , testGroup "Pairing properties"
         [ test_pairing_left_additive
         , test_pairing_right_additive
         , test_pairing_balanced
         , test_random_pairing
         ]
        ]


