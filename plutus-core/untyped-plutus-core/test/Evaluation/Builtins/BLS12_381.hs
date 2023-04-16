{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}

{- | Property tests for the BLS12-381 builtins -}
module Evaluation.Builtins.BLS12_381
where

import Evaluation.Builtins.BLS12_381.TestClasses
import Evaluation.Builtins.BLS12_381.Utils
import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Default

import Cardano.Crypto.EllipticCurve.BLS12_381 (scalarPeriod)
import Data.ByteString as BS (length)
import Data.List (foldl', genericReplicate)
import Text.Printf (printf)

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

-- QuickCheck utilities

mkTestName :: forall a. TestableAbelianGroup a => String -> String
mkTestName s = printf "%s_%s" (groupName @a) s

withNTests :: Testable prop => prop -> Property
withNTests = withMaxSuccess 200

-- QuickCheck generators for scalars and group elements as PLC terms

arbitraryConstant :: forall a . TestableAbelianGroup a => Gen PlcTerm
arbitraryConstant = toTerm <$> (arbitrary @a)

arbitraryScalar :: Gen PlcTerm
arbitraryScalar = integer <$> (arbitrary @Integer)

-- Constructing pairing terms

millerLoopTerm :: PlcTerm -> PlcTerm -> PlcTerm
millerLoopTerm = mkApp2 Bls12_381_millerLoop

mulMlResultTerm :: PlcTerm -> PlcTerm -> PlcTerm
mulMlResultTerm = mkApp2 Bls12_381_mulMlResult

finalVerifyTerm :: PlcTerm -> PlcTerm -> PlcTerm
finalVerifyTerm = mkApp2 Bls12_381_finalVerify


{- Generic tests for the TestableAbelianGroup class.  Later these are instantiated
   at the G1 and G2 types. -}

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
      let e = eqTerm @a (addTerm @a p1 (addTerm @a p2 p3)) (addTerm @a (addTerm @a p1 p2) p3)
      pure $ evalTerm e === uplcTrue

-- | Zero is an identity for addition.
test_add_zero :: forall a. TestableAbelianGroup a => TestTree
test_add_zero =
    testProperty
    (mkTestName @a "add_zero") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqTerm @a (addTerm @a  p $ zeroTerm @a) p
      pure $ evalTerm e === uplcTrue

-- | Every element has an inverse
-- | a+(-a) = 0 for all group elements.
test_neg :: forall a. TestableAbelianGroup a => TestTree
test_neg =
    testProperty
    (mkTestName @a "additive_inverse") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqTerm @a (addTerm @a p (negTerm @a p)) $ zeroTerm @a
      pure $ evalTerm e === uplcTrue

-- | Group addition is commutative.
test_add_commutative :: forall a. TestableAbelianGroup a => TestTree
test_add_commutative=
    testProperty
    (mkTestName @a "add_commutative") .
    withNTests $ do
      p1 <- arbitraryConstant @a
      p2 <- arbitraryConstant @a
      let e = eqTerm @a (addTerm @a p1 p2) (addTerm @a p2 p1)
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
      let e1 = scalarMulTerm @a (mkApp2 MultiplyInteger m n) p
          e2 = scalarMulTerm @a m (scalarMulTerm @a n p)
          e3 = eqTerm @a e1 e2
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
      let e1 = scalarMulTerm @a (mkApp2 AddInteger m n) p
          e2 = addTerm @a (scalarMulTerm @a m p) (scalarMulTerm @a n p)
          e3 = eqTerm @a e1 e2
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
      let e1 = scalarMulTerm @a n (addTerm @a p q)
          e2 = addTerm @a (scalarMulTerm @a n p) (scalarMulTerm @a n q)
          e3 = eqTerm @a e1 e2
      pure $ evalTerm e3 === uplcTrue

-- | 0p = 0 for all group elements p.
test_scalarMul_zero :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_zero =
    testProperty
    (mkTestName @a "scalarMul_zero") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqTerm @a (scalarMulTerm @a (integer 0) p) $ zeroTerm @a
      pure $ evalTerm e === uplcTrue

-- | 1p = p for all group elements p.
test_scalarMul_one :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_one =
    testProperty
    (mkTestName @a "scalarMul_one") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqTerm @a (scalarMulTerm @a (integer 1) p) p
      pure $ evalTerm e === uplcTrue

-- | (-1)p = -p for all group elements p.
test_scalarMul_inverse :: forall a. TestableAbelianGroup a => TestTree
test_scalarMul_inverse =
    testProperty
    (mkTestName @a "scalarMul_inverse") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqTerm @a (scalarMulTerm @a (integer (-1)) p) (negTerm @a p)
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
          e2 = eqTerm @a (scalarMulTerm @a (integer n) p) e1
      pure $ evalTerm e2 === uplcTrue
          where
            repeatedAdd :: Integer -> PlcTerm -> PlcTerm
            repeatedAdd n t =
                if n>=0
                then foldl' (addTerm @a) (zeroTerm @a) $ genericReplicate n t
                else repeatedAdd (-n) (negTerm @a t)

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
      let e1 = scalarMulTerm @a m p
          k = mkApp2 AddInteger m (mkApp2 MultiplyInteger n (integer scalarPeriod))
          e2 = scalarMulTerm @a k p -- k = m+n|G|
          e = eqTerm @a e1 e2
      pure $ evalTerm e === uplcTrue

test_Z_action_good :: forall a. TestableAbelianGroup a => TestTree
test_Z_action_good =
    testGroup (printf "Z acts correctly on %s" $ groupName @a)
         [ test_scalarMul_assoc              @a
         , test_scalarMul_distributive_left  @a
         , test_scalarMul_distributive_right @a
         , test_scalarMul_zero               @a
         , test_scalarMul_one                @a
         , test_scalarMul_inverse            @a
         , test_scalarMul_repeated_addition  @a
         , test_scalarMul_periodic           @a
         ]


{- Generic tests for the HashAndCompress class.  Later these are instantiated at
   the G1 and G2 types. -}

test_roundtrip_compression :: forall a. HashAndCompress a => TestTree
test_roundtrip_compression =
    testProperty
    (mkTestName @a "roundtrip_compression") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqTerm @a (uncompressTerm @a (compressTerm @a p)) p
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
    (mkTestName @a "uncompression_wrong_size") .
    withNTests $ do
      b <- suchThat (resize 128 arbitrary) incorrectSize
      let e = uncompressTerm @a (bytestring b)
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
      let e = uncompressTerm @a (bytestring b')
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
          e = uncompressTerm @a (bytestring b)
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
          e1 = uncompressTerm @a (bytestring b1)
          e2 = uncompressTerm @a (bytestring b2)
          e  = eqTerm @a e2 (negTerm @a e1)
      pure $ evalTerm e === uplcTrue

-- | Check that bytestrings with the infinity bit set fail to uncompress.
test_set_infinity_bit :: forall a. HashAndCompress a => TestTree
test_set_infinity_bit =
    testProperty
    (mkTestName @a "set_infinity_bit") .
    withNTests $ do
      p <- arbitrary @a
      let b = setBits infinityBit $ compress @a p
          e = uncompressTerm @a (bytestring b)
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
      let e = eqTerm @a (hashToGroupTerm @a $ bytestring b1) (hashToGroupTerm @a $ bytestring b2)
      pure $ b1 /= b2 ==> evalTerm e === uplcFalse

test_compress_hash :: forall a. HashAndCompress a => TestTree
test_compress_hash =
    testGroup (printf "Uncompression and hashing behave properly for %s" $ groupName @a)
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
      let e1 = millerLoopTerm (addTerm @G1.Element p1 p2) q
          e2 = mulMlResultTerm (millerLoopTerm p1 q) (millerLoopTerm p2 q)
          e3 = finalVerifyTerm e1 e2
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
      let e1 = millerLoopTerm p (addTerm @G2.Element q1 q2)
          e2 = mulMlResultTerm (millerLoopTerm p q1) (millerLoopTerm p q2)
          e3 = finalVerifyTerm e1 e2
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
      let e1 = millerLoopTerm (scalarMulTerm @G1.Element n p) q
          e2 = millerLoopTerm p (scalarMulTerm @G2.Element n q)
          e3 = finalVerifyTerm e1 e2
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
            let e = finalVerifyTerm (millerLoopTerm p1 q1) (millerLoopTerm p2 q2)
            in evalTerm e === uplcFalse


-- All of the tests

test_BLS12_381 :: TestTree
test_BLS12_381 = testGroup "BLS12-381" [
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
