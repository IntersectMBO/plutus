{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}

module Evaluation.Builtins.BLS12_381.HaskellTests (tests)
where

import Evaluation.Builtins.BLS12_381.Common
import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2
import PlutusCore.BLS12_381.GT qualified as GT

import Crypto.EllipticCurve.BLS12_381 (BLSTError)
import Data.ByteString as BS (length)
import Data.Either (isLeft)
import Data.List (foldl', genericReplicate)
import Text.Printf (printf)

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck


---------------- G is an Abelian group ----------------

-- | Group addition is associative.
prop_add_assoc :: forall a. TestableAbelianGroup a => TestTree
prop_add_assoc =
    testProperty
    (mkTestName @a "add_assoc") .
    withNTests $ do
      p1 <- arbitrary @a
      p2 <- arbitrary
      p3 <- arbitrary
      pure $ add p1 (add p2 p3) === add (add p1 p2) p3

-- | Zero is an identity for addition.
prop_add_zero :: forall a. TestableAbelianGroup a => TestTree
prop_add_zero =
    testProperty
    (mkTestName @a "add_zero") .
    withNTests $ do
      p <- arbitrary @a
      pure $ p === add p zero

-- | Every element has an inverse
-- | a+(-a) = 0 for all group elements.
prop_neg :: forall a. TestableAbelianGroup a => TestTree
prop_neg =
    testProperty
    (mkTestName @a "additive_inverse") .
    withNTests $ do
      p <- arbitrary @a
      pure $ add p (neg p) === zero

-- | Group addition is commutative.
prop_add_commutative :: forall a. TestableAbelianGroup a => TestTree
prop_add_commutative =
    testProperty
    (mkTestName @a "add_commutative") .
    withNTests $ do
      p1 <- arbitrary @a
      p2 <- arbitrary
      pure $ add p1 p2 === add p2 p1

test_is_an_abelian_group :: forall a. TestableAbelianGroup a => TestTree
test_is_an_abelian_group =
    testGroup (mkTestName @a "is_an_abelian_group")
         [ prop_add_assoc       @a
         , prop_add_zero        @a
         , prop_neg             @a
         , prop_add_commutative @a
         ]


---------------- Z acts on G correctly ----------------

-- | (ab)p = a(bp) for all scalars a and b and all group elements p.
prop_scalar_assoc :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_assoc =
    testProperty
    (mkTestName @a "scalar_mul_assoc") .
    withNTests $ do
      a <- arbitrary
      b <- arbitrary
      p <- arbitrary @a
      pure $ mul (a*b) p === mul a (mul b p)

-- | (a+b)p = ap +bp for all scalars a and b and all group elements p.
prop_scalar_distributive_left :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_distributive_left =
    testProperty
    (mkTestName @a "scalar_distributive_left") .
    withNTests $  do
      a <- arbitrary
      b <- arbitrary
      p <- arbitrary @a
      pure $ mul (a+b) p === add (mul a p) (mul b p)

-- | a(p+q) = ap + aq for all scalars a and all group elements p and q.
prop_scalar_distributive_right :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_distributive_right =
    testProperty
    (mkTestName @a "scalar_distributive") .
    withNTests $  do
      a <- arbitrary
      p <- arbitrary @a
      q <- arbitrary
      pure $ mul a (add p q) === add (mul a p) (mul a q)

-- | 0p = 0 for all group elements p.
prop_scalar_zero :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_zero =
    testProperty
    (mkTestName @a "scalar_zero") .
    withNTests $ do
      p <- arbitrary @a
      pure $ mul 0 p === zero

-- | 1p = p for all group elements p.
prop_scalar_identity :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_identity =
    testProperty
    (mkTestName @a "scalar_identity") .
    withNTests $ do
      p <- arbitrary @a
      pure $ mul 1 p === p

-- | (-1)p = -p for all group elements p.
prop_scalar_inverse :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_inverse =
    testProperty
    (mkTestName @a "scalar_inverse") .
    withNTests $ property $ do
      p <- arbitrary @a
      pure $ neg p === mul (-1) p

-- Check that scalar multiplication is repeated addition (including negative
-- scalars). We should really check this for scalars greater than the group
-- order, but that would be prohibitively slow because the order of G1 and G2
-- has 256 bits (about 5*10^76).
prop_scalar_multiplication :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_multiplication =
    testProperty
    (mkTestName @a "scalar_multiplication") .
    withNTests $ do
      n <- resize 10000 arbitrary
      p <- arbitrary @a
      pure $ mul n p === repeatedAdd n p
          where repeatedAdd :: Integer -> a -> a
                repeatedAdd n p =
                    if n >= 0
                    then foldl' add zero $ genericReplicate n p
                    else repeatedAdd (-n) (neg p)

test_Z_action_good :: forall a. TestableAbelianGroup a => TestTree
test_Z_action_good =
    testGroup (printf "Z acts correctly on %s" $ gname @a)
         [ prop_scalar_assoc              @a
         , prop_scalar_distributive_left  @a
         , prop_scalar_distributive_right @a
         , prop_scalar_zero               @a
         , prop_scalar_identity           @a
         , prop_scalar_inverse            @a
         , prop_scalar_multiplication     @a
         ]


---------------- Compression, uncompression, and hashing work properly ----------------

-- | Check that if we compress a group element then it will always uncompress
-- succesfully and give you back the same thing.
prop_roundtrip_compression :: forall e a. HashAndCompress e a => TestTree
prop_roundtrip_compression =
    testProperty
    (mkTestName @a "roundtrip_compression") .
    withNTests $ do
      p <- arbitrary @a
      case uncompress @e @a $ compress @e @a p of
        Left e  -> error $ show e
        Right q -> pure $ p === q

-- | Uncompression should only accept inputs of the expected length, so we check
-- it on random inputs of the incorrect length.  Inputs of the expected length
-- are excluded by the incorrectSize predicate; however even if an input did
-- have the expected length it would be very unlikely to deserialise to a point
-- in the group because the cofactors are very big (7.6*10^37 for G1 and
-- 3.1*10^152 for G2).
prop_uncompression_input_size :: forall e a. HashAndCompress e a => TestTree
prop_uncompression_input_size =
    testProperty
    (mkTestName @a "uncompression_input_size") .
    withNTests $ do
      b <- suchThat (resize 128 arbitrary) incorrectSize
      pure $ isLeft $ uncompress @e @a b
    where incorrectSize s =
              BS.length s /= compressedSize @e @a

-- | This tests the case we've omitted in the previous test, and should fail
-- with very high probablity.  Ideally we'd check that the point really isn't in
-- the group, but we can't do that until we've uncompressed it anyway.
prop_uncompress_out_of_group :: forall e a. HashAndCompress e a => TestTree
prop_uncompress_out_of_group =
    testProperty
    (mkTestName @a "uncompress_out_of_group") .
    withNTests $ do
      b <- resize (compressedSize @e @a) arbitrary
      pure $ isLeft $ uncompress @e @a b

-- | Hashing into G1 or G2 should be collision-free. A failure here would be
-- interesting.
prop_no_hash_collisions :: forall e a. HashAndCompress e a => TestTree
prop_no_hash_collisions =
    testProperty
    (mkTestName @a "no_hash_collisions") .
    withNTests $ do
      b1 <- arbitrary
      b2 <- arbitrary
      pure $ b1 /= b2 ==> hashTo @e @a b1 =/= hashTo @e @a b2

test_compress_hash :: forall e a. HashAndCompress e a => TestTree
test_compress_hash =
    testGroup (printf "Uncompression and hashing behave properly for %s" $ gname @a)
         [ prop_roundtrip_compression    @e @a
         , prop_uncompression_input_size @e @a
         , prop_uncompress_out_of_group  @e @a
         , prop_no_hash_collisions       @e @a
         ]


---------------- Pairing tests ----------------

pairing :: G1.Element -> G2.Element -> GT.Element
pairing p q =
    case GT.pairing p q of
      Left e  -> error $ show e
      Right r -> r

-- <p1+p2,q> = <p1,q>.<p2,q>
prop_pairing_left_additive :: TestTree
prop_pairing_left_additive =
    testProperty
    "pairing_left_additive" .
    withNTests $ do
      p1 <- arbitrary
      p2 <- arbitrary
      q  <- arbitrary
      let e1 = pairing (add p1 p2) q
          e2 = GT.mul (pairing p1 q) (pairing p2 q)
      pure $ GT.finalVerify e1 e2 === True

-- <p,q1+q2> = <p,q1>.<p,q2>
prop_pairing_right_additive :: TestTree
prop_pairing_right_additive =
    testProperty
    "pairing_right_additive" .
    withNTests $ do
      p <-  arbitrary
      q1 <- arbitrary
      q2 <- arbitrary
      let e1 = pairing p (G2.add q1 q2)
          e2 = GT.mul (pairing p q1) (pairing p q2)
      pure $ GT.finalVerify e1 e2 === True

-- <[n]p,q> = <p,[n]q> for all n in Z, p in G1, q in G2.
-- We could also test that both of these are equal to <p,q>^n, but we don't have
-- an exponentiation function in GT.  We could implement exponentiation using GT
-- multiplication, but that would require some work.
prop_pairing_balanced :: TestTree
prop_pairing_balanced =
     testProperty
     "pairing_balanced" .
     withNTests $ do
       n <-  arbitrary
       p <-  arbitrary
       q <-  arbitrary
       pure $ GT.finalVerify (pairing (mul n p) q) (pairing p (mul n q)) === True

-- finalVerify returns False for random inputs
prop_random_pairing :: TestTree
prop_random_pairing =
    testProperty
    "pairing_random_unequal" .
    withNTests $
    do
       a  <- arbitrary @G1.Element
       b  <- arbitrary @G2.Element
       a' <- arbitrary
       b' <- arbitrary
       pure $ a /= a' && b /= b' ==>
            GT.finalVerify (doPairing a b) (doPairing a' b') === False
                where doPairing p q =
                          case GT.pairing p q of
                            Left e  -> error $ show e
                            Right r -> r

-- All the tests

tests :: TestTree
tests = testGroup "*** Haskell property tests ***" [
         testGroup "G1 properties"
         [ test_is_an_abelian_group @G1.Element
         , test_Z_action_good       @G1.Element
         , test_compress_hash       @BLSTError @G1.Element
         ]

        , testGroup "G2 properties"
         [ test_is_an_abelian_group @G2.Element
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

