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
import Data.String (fromString)
import Text.Printf (printf)

import Hedgehog hiding (Group (..))
import Hedgehog.Gen qualified as Gen

import Test.Tasty
import Test.Tasty.Hedgehog

---------------- G is an Abelian group ----------------

prop_assoc :: forall a. TestableAbelianGroup a => TestTree
prop_assoc =
    testPropertyNamed
    (printf "Addition in %s is associative" name)
    (fromString $ printf "%s_assoc" name) .
    withNTests $ property $ do
      p1 <- forAll $ genElement @a
      p2 <- forAll $ genElement
      p3 <- forAll $ genElement
      add p1 (add p2 p3) === add (add p1 p2) p3
        where name = gname @a

prop_zero :: forall a. TestableAbelianGroup a => TestTree
prop_zero =
    testPropertyNamed
    (printf "The zero element is the additive identity in %s" name)
    (fromString $ printf "%s_zero" name) .
    withNTests $ property $ do
      p <- forAll $ genElement @a
      p === add p zero
        where name = gname @a

prop_neg :: forall a. TestableAbelianGroup a => TestTree
prop_neg =
    testPropertyNamed
    (printf "Every point in %s has an additive inverse" name)
    (fromString $ printf "%s_inverse" name) .
    withNTests $ property $ do
      p <- forAll  $ genElement @a
      add p (neg p) === zero
        where name = gname @a

prop_abelian :: forall a. TestableAbelianGroup a => TestTree
prop_abelian =
    testPropertyNamed
    (printf "Addition in %s is commutative" name)
    (fromString $ printf "%s_abelian" name) .
    withNTests $ property $ do
      p1 <- forAll $ genElement @a
      p2 <- forAll $ genElement
      add p1 p2 === add p2 p1
        where name = gname @a

test_is_an_Abelian_group :: forall a. TestableAbelianGroup a => TestTree
test_is_an_Abelian_group =
    testGroup (printf "%s is an Abelian group" name)
         [ prop_assoc   @a
         , prop_zero    @a
         , prop_neg     @a
         , prop_abelian @a
         ]
        where name = gname @a

---------------- Z acts on G correctly ----------------

prop_scalar_assoc :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_assoc =
    testPropertyNamed
    (printf "Scalar multiplication is associative in %s" name)
    (fromString $ printf "%s_scalar_assoc" name) .
    withNTests $ withShrinks 0 $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll $ genElement @a
      mul (a*b) p === mul a (mul b p)
        where name = gname @a

prop_scalar_zero :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_zero =
    testPropertyNamed
    (printf "Scalar multiplication by 0 always yields the zero element of %s" name)
    (fromString $ printf "%s_scalar_zero" name) .
    withNTests $ property $ do
      p <- forAll $ genElement @a
      mul 0 p === zero
        where name = gname @a

prop_scalar_identity :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_identity =
    testPropertyNamed
    (printf "Scalar multiplication by 1 is the identity function on %s" name)
    (fromString $ printf "%s_scalar_identity" name) .
    withNTests $ property $ do
      p <- forAll $ genElement @a
      mul 1 p === p
        where name = gname @a

prop_scalar_inverse :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_inverse =
    testPropertyNamed
    (printf "-p = (-1)*p for all p in %s" name)
    (fromString $ printf "%s_scalar_inverse" $ gname @a) .
    withNTests $ withShrinks 0 $ property $ do
      p <- forAll $ genElement @a
      neg p === mul (-1) p
        where name = gname @a

prop_scalar_distributive :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_distributive =
    testPropertyNamed
    (printf "Scalar multiplication distributes over addition in %s" name)
    (fromString $ printf "%s_scalar_distributive" name) .
    withNTests $ withShrinks 0 $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll $ genElement @a
      mul (a+b) p === add (mul a p) (mul b p)
        where name = gname @a

prop_scalar_multiplication :: forall a. TestableAbelianGroup a => TestTree
prop_scalar_multiplication = let name = gname @a in
    testPropertyNamed
    (printf "Scalar multiplication is repeated addition in %s" name)
    (fromString $ printf "%s_scalar_multiplication" name) .
    withNTests $ withShrinks 0 $ property $ do
      n <- forAll genSmallScalar
      p <- forAll $ genElement @a
      mul n p === repeatedAdd n p
          where repeatedAdd :: Integer -> a -> a
                repeatedAdd n p =
                    if n >= 0
                    then foldl' add (zero @a) $ genericReplicate n p
                    else repeatedAdd (-n) (neg p)

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
      p <- forAll $ genElement @a
      case uncompress @e @a $ compress @e @a p of
        Left e  -> error $ show e
        Right q -> p === q
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
      b <- forAll $ Gen.filter (\x -> BS.length x /= expectedSize) $ genByteString100
      assert $ isLeft $ uncompress @e @a b
    where name = gname @a
          expectedSize = fromIntegral $ compressedSize @e @a

prop_hash :: forall e a. HashAndCompress e a => TestTree
prop_hash =
    testPropertyNamed
    (printf "Different inputs hash to different points in %s" name)
    (fromString $ printf "%s_no_hash_collisions" name) .
    withNTests $
    withShrinks 0 $
    property $ do
      b1 <- forAll genByteString
      b2 <- forAll $ Gen.filter (/= b1) genByteString  -- Does this do what I think it does?
      hashTo @e @a b1 /== hashTo @e @a b2
        where name = gname @a

test_compress_hash :: forall e a. HashAndCompress e a => TestTree
test_compress_hash =
    testGroup (printf "Uncompression and hashing behave properly for %s" $ gname @a)
         [ prop_roundtrip_compression @e @a
         , prop_uncompression_input_size @e @a
         , prop_hash @e @a
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
    testPropertyNamed
    "Pairing is left additive"
    "pairing_left_additive" .
    withNTests $ withShrinks 0 $ property $ do
      p1 <- forAll genElement
      p2 <- forAll genElement
      q <- forAll genElement
      let e1 = pairing (add p1 p2) q
          e2 = GT.mul (pairing p1 q) (pairing p2 q)
      GT.finalVerify e1 e2 === True

-- <p,q1+q2> = <p,q1>.<p,q2>
prop_pairing_right_additive :: TestTree
prop_pairing_right_additive =
    testPropertyNamed
    "Pairing is right additive"
    "pairing_right_additive" .
    withNTests $ withShrinks 0 $ property $ do
      p <- forAll genElement
      q1 <- forAll genElement
      q2 <- forAll genElement
      let e1 = pairing p (G2.add q1 q2)
          e2 = GT.mul (pairing p q1) (pairing p q2)
      GT.finalVerify e1 e2 === True

-- <[n]p,q> = <p,[n]q> for all n in Z, p in G1, q in G2.
-- We could also test that both of these are equal to <p,q>^n, but we don't have
-- an exponentiation function in GT.  We could implement exponentiation using GT
-- multiplication, but that would require some work.
prop_pairing_balanced :: TestTree
prop_pairing_balanced =
     testPropertyNamed
     "Pairing is balanced"
     "pairing_balanced" .
     withTests 100 $ withShrinks 0 $ property $ do
       n <- forAll genScalar
       p <- forAll $ genElement @G1.Element
       q <- forAll $ genElement @G2.Element
       GT.finalVerify (pairing (mul n p) q) (pairing p (mul n q)) === True

prop_random_pairing :: TestTree
prop_random_pairing =
    testPropertyNamed
    "Pairings of random points are unequal"
    "pairing_random" .
    withNTests $
    withShrinks 0 $
    property $ do
       a <- forAll $ genElement @G1.Element
       b <- forAll $ genElement @G2.Element
       a' <- forAll $ Gen.filter (/= a) genElement
       b' <- forAll $ Gen.filter (/= b) genElement
       let x = case GT.pairing a b of
                 Left e   -> error $ show e
                 Right xx -> xx
       let y = case GT.pairing a' b' of
                 Left e   -> error $ show e
                 Right yy -> yy
       GT.finalVerify x y === False


-- All the tests

tests :: TestTree
tests = testGroup "*** Haskell property tests ***" [
         testGroup "G1 properties"
         [ test_is_an_Abelian_group @G1.Element
         , test_Z_action_good @G1.Element
         , test_compress_hash @BLSTError @G1.Element
         ]

        , testGroup "G2 properties"
         [ test_is_an_Abelian_group @G2.Element
         , test_Z_action_good @G2.Element
         , test_compress_hash @BLSTError @G2.Element
         ]
        , testGroup "Pairing properties"
         [ prop_pairing_left_additive
         , prop_pairing_right_additive
         , prop_pairing_balanced
         , prop_random_pairing
         ]
        ]

