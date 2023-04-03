{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}

module Evaluation.Builtins.BLS12_381.HaskellTests (tests)
where

import Evaluation.Builtins.BLS12_381.Common
import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as Pairing

import Cardano.Crypto.EllipticCurve.BLS12_381 (BLSTError (..), scalarPeriod)
import Data.ByteString as BS (length)
import Data.List (foldl', genericReplicate)
import Text.Printf (printf)

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck


---------------- G is an Abelian group ----------------

-- | Group addition is associative.
test_add_assoc :: forall a. TestableAbelianGroup a => TestTree
test_add_assoc =
    testProperty
    (mkTestName @a "add_assoc") .
    withNTests $ do
      p1 <- arbitrary @a
      p2 <- arbitrary
      p3 <- arbitrary
      pure $ add p1 (add p2 p3) === add (add p1 p2) p3

-- | Zero is an identity for addition.
test_add_zero :: forall a. TestableAbelianGroup a => TestTree
test_add_zero =
    testProperty
    (mkTestName @a "add_zero") .
    withNTests $ do
      p <- arbitrary @a
      pure $ p === add p zero

-- | Every element has an inverse
-- | a+(-a) = 0 for all group elements.
test_neg :: forall a. TestableAbelianGroup a => TestTree
test_neg =
    testProperty
    (mkTestName @a "additive_inverse") .
    withNTests $ do
      p <- arbitrary @a
      pure $ add p (neg p) === zero

-- | Group addition is commutative.
test_add_commutative :: forall a. TestableAbelianGroup a => TestTree
test_add_commutative =
    testProperty
    (mkTestName @a "add_commutative") .
    withNTests $ do
      p1 <- arbitrary @a
      p2 <- arbitrary
      pure $ add p1 p2 === add p2 p1

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
    (mkTestName @a "scalarMul_assoc") .
    withNTests $ do
      m <- arbitrary
      n <- arbitrary
      p <- arbitrary @a
      pure $ scalarMul (m*n) p === scalarMul m (scalarMul n p)

-- | (a+b)p = ap +bp for all scalars a and b and all group elements p.
test_scalarMul_distributive_left :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_distributive_left =
    testProperty
    (mkTestName @a "scalarMul_distributive_left") .
    withNTests $  do
      m <- arbitrary
      n <- arbitrary
      p <- arbitrary @a
      pure $ scalarMul (m+n) p === add (scalarMul m p) (scalarMul n p)

-- | a(p+q) = ap + aq for all scalars a and all group elements p and q.
test_scalarMul_distributive_right :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_distributive_right =
    testProperty
    (mkTestName @a "scalarMul_distributive_right") .
    withNTests $  do
      n <- arbitrary
      p <- arbitrary @a
      q <- arbitrary
      pure $ scalarMul n (add p q) === add (scalarMul n p) (scalarMul n q)

-- | 0p = 0 for all group elements p.
test_scalarMul_zero :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_zero =
    testProperty
    (mkTestName @a "scalarMul_zero") .
    withNTests $ do
      p <- arbitrary @a
      pure $ scalarMul 0 p === zero

-- | 1p = p for all group elements p.
test_scalarMul_one :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_one =
    testProperty
    (mkTestName @a "scalarMul_one") .
    withNTests $ do
      p <- arbitrary @a
      pure $ scalarMul 1 p === p

-- | (-1)p = -p for all group elements p.
test_scalarMul_inverse :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_inverse =
    testProperty
    (mkTestName @a "scalarMul_inverse") .
    withNTests $ property $ do
      p <- arbitrary @a
      pure $ neg p === scalarMul (-1) p

-- Check that scalar multiplication is repeated addition (including negative
-- scalars). We should really check this for scalars greater than the group
-- order, but that would be prohibitively slow because the order of G1 and G2
-- has 256 bits (about 5*10^76).
test_scalarMul_repeated_addition :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_repeated_addition =
    testProperty
    (mkTestName @a "scalarMul_repeated_addition") .
    withNTests $ do
      n <- resize 10000 arbitrary
      p <- arbitrary @a
      pure $ scalarMul n p === repeatedAdd n p
          where repeatedAdd :: Integer -> a -> a
                repeatedAdd n p =
                    if n >= 0
                    then foldl' add zero $ genericReplicate n p
                    else repeatedAdd (-n) (neg p)

-- (m + n|G|)p = mp for all group elements p and integers m and n.
-- We have |G1| = |G2| = scalarPeriod
test_scalarMul_periodic :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_periodic =
    testProperty
    (mkTestName @a "scalarMul_periodic") .
    withNTests $ do
      m <- arbitrary
      n <- arbitrary
      p <- arbitrary @a
      pure $ scalarMul m p === scalarMul (m+n*scalarPeriod) p

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

-- | Check that if we compress a group element then it will always uncompress
-- succesfully and give you back the same thing.
test_roundtrip_compression :: forall a . HashAndCompress a => TestTree
test_roundtrip_compression =
    testProperty
    (mkTestName @a "roundtrip_compression") .
    withNTests $ do
      p <- arbitrary @a
      case uncompress @a $ compress @a p of
        Left e  -> error $ show e
        Right q -> pure $ p === q

-- | Uncompression should only accept inputs of the expected length, so we check
-- it on random inputs of the incorrect length.  Inputs of the expected length
-- are excluded by the incorrectSize predicate; however even if an input did
-- have the expected length it would be very unlikely to deserialise to a point
-- in the group because the cofactors are very big (7.6*10^37 for G1 and
-- 3.1*10^152 for G2).
test_uncompression_wrong_size :: forall a . HashAndCompress a => TestTree
test_uncompression_wrong_size =
    testProperty
    (mkTestName @a "uncompression_wrong_size") .
    withNTests $ do
      b <- suchThat (resize 128 arbitrary) incorrectSize
      pure $ uncompress @a b == Left BLST_BAD_ENCODING
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
          r = uncompress @a b'
      pure $ r === Left BLST_BAD_ENCODING .||.
             r === Left BLST_POINT_NOT_ON_CURVE .||.
             r === Left BLST_POINT_NOT_IN_GROUP
    where correctSize s = BS.length s == compressedSize @a

-- | Check that the most significant bit is set for all compressed points
test_compression_bit_set :: forall a. HashAndCompress a => TestTree
test_compression_bit_set =
    testProperty
    (mkTestName @a "compression_bit_set") .
    withNTests $ do
      p <- arbitrary @a
      pure $ isSet compressionBit $ compress @a p

-- | Check that bytestrings with the compression bit clear fail to uncompress.
test_clear_compression_bit :: forall a. HashAndCompress a => TestTree
test_clear_compression_bit =
    testProperty
    (mkTestName @a "clear_compression_bit") .
    withNTests $ do
      p <- arbitrary @a
      let b = clearBits compressionBit $ compress @a p
      pure $ uncompress @a b === Left BLST_BAD_ENCODING

-- | Check that flipping the sign bit in a compressed point gives the inverse of
-- the point.
test_flip_sign_bit :: forall a. HashAndCompress a => TestTree
test_flip_sign_bit =
    testProperty
    (mkTestName @a "flip_sign_bit") .
    withNTests $ do
      p <- arbitrary @a
      let b = flipBits signBit $ compress @a p
      pure $ uncompress @a b === (Right $ neg @a p)

-- | Check that bytestrings with the infinity bit set fail to uncompress.
test_set_infinity_bit :: forall a. HashAndCompress a => TestTree
test_set_infinity_bit =
    testProperty
    (mkTestName @a "set_infinity_bit") .
    withNTests $ do
      p <- arbitrary @a
      let b = setBits infinityBit $ compress @a p
      pure $ uncompress @a b === Left BLST_BAD_ENCODING

-- | Hashing into G1 or G2 should be collision-free. A failure here would be
-- interesting.
test_no_hash_collisions :: forall a . HashAndCompress a => TestTree
test_no_hash_collisions =
    testProperty
    (mkTestName @a "no_hash_collisions") .
    withNTests $ do
      b1 <- arbitrary
      b2 <- arbitrary
      pure $ b1 /= b2 ==> hashTo @a b1 =/= hashTo @a b2

test_compress_hash :: forall a . HashAndCompress a => TestTree
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


---------------- Pairing tests ----------------
-- | Tests for the BLS12-381 pairing operations.  These are a little difficult
-- to test directly because we don't have direct access to elements of MlResult.
-- The best we can do is to check elements (which can only be constructed by the
-- pairing operation and multiplication in MlResult) using finalVerify.

-- <p1+p2,q> = <p1,q>.<p2,q>
test_pairing_left_additive :: TestTree
test_pairing_left_additive =
    testProperty
    "pairing_left_additive" .
    withNTests $ do
      p1 <- arbitrary
      p2 <- arbitrary
      q  <- arbitrary
      let e1 = Pairing.millerLoop (add p1 p2) q
          e2 = Pairing.mulMlResult (Pairing.millerLoop p1 q) (Pairing.millerLoop p2 q)
      pure $ Pairing.finalVerify e1 e2 === True

-- <p,q1+q2> = <p,q1>.<p,q2>
test_pairing_right_additive :: TestTree
test_pairing_right_additive =
    testProperty
    "pairing_right_additive" .
    withNTests $ do
      p <-  arbitrary
      q1 <- arbitrary
      q2 <- arbitrary
      let e1 = Pairing.millerLoop p (G2.add q1 q2)
          e2 = Pairing.mulMlResult (Pairing.millerLoop p q1) (Pairing.millerLoop p q2)
      pure $ Pairing.finalVerify e1 e2 === True

-- <[n]p,q> = <p,[n]q> for all n in Z, p in G1, q in G2.
-- We could also test that both of these are equal to <p,q>^n, but we don't have
-- an exponentiation function in GT.  We could implement exponentiation using GT
-- multiplication, but that would require some work.
test_pairing_balanced :: TestTree
test_pairing_balanced =
     testProperty
     "pairing_balanced" .
     withNTests $ do
       n <-  arbitrary
       p <-  arbitrary
       q <-  arbitrary
       pure $ Pairing.finalVerify
                (Pairing.millerLoop (scalarMul n p) q)
                (Pairing.millerLoop p (scalarMul n q))
                === True

-- finalVerify returns False for random inputs
test_random_pairing :: TestTree
test_random_pairing =
    testProperty
    "pairing_random_unequal" .
    withNTests $
    do
       a  <- arbitrary @G1.Element
       b  <- arbitrary @G2.Element
       a' <- arbitrary
       b' <- arbitrary
       pure $ a /= a' && b /= b' ==>
            Pairing.finalVerify (Pairing.millerLoop a b) (Pairing.millerLoop a' b') === False

-- All the tests

tests :: TestTree
tests = testGroup "*** Haskell property tests ***" [
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

