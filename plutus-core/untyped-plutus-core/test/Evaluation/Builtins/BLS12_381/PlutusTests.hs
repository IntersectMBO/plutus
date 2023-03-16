{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}

module Evaluation.Builtins.BLS12_381.PlutusTests (tests)
where

import Evaluation.Builtins.BLS12_381.Common
import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2
import PlutusCore.Default

import Crypto.EllipticCurve.BLS12_381 (BLSTError, scalarPeriod)
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

prop_add_assoc :: forall a. TestableAbelianGroup a => TestTree
prop_add_assoc =
    testProperty
    (mkTestName @a "add_assoc") .
    withNTests $ do
      p1 <- arbitraryConstant @a
      p2 <- arbitraryConstant @a
      p3 <- arbitraryConstant @a
      let e = eqP @a (addP @a p1 (addP @a p2 p3)) (addP @a (addP @a p1 p2) p3)
      pure $ evalTerm e === uplcTrue

prop_add_zero :: forall a. TestableAbelianGroup a => TestTree
prop_add_zero =
    testProperty
    (mkTestName @a "add_zero") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (addP @a  p $ zeroP @a) p
      pure $ evalTerm e === uplcTrue

prop_neg :: forall a. TestableAbelianGroup a => TestTree
prop_neg =
    testProperty
    (mkTestName @a "additive_inverse") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (addP @a p (negP @a p)) $ zeroP @a
      pure $ evalTerm e === uplcTrue

prop_add_commutative :: forall a. TestableAbelianGroup a => TestTree
prop_add_commutative=
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
              [ prop_add_assoc       @a
              , prop_add_zero        @a
              , prop_neg             @a
              , prop_add_commutative @a
              ]


---------------- Z acts on G correctly ----------------

prop_scalarMul_assoc :: forall a. TestableAbelianGroup a => TestTree
prop_scalarMul_assoc =
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

prop_scalarMul_distributive_left :: forall a. TestableAbelianGroup a => TestTree
prop_scalarMul_distributive_left =
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

prop_scalarMul_distributive_right :: forall a. TestableAbelianGroup a => TestTree
prop_scalarMul_distributive_right =
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

prop_scalarMul_zero :: forall a. TestableAbelianGroup a => TestTree
prop_scalarMul_zero =
    testProperty
    (mkTestName @a "scalarMul_zero") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (scalarMulP @a (integer 0) p) $ zeroP @a
      pure $ evalTerm e === uplcTrue

prop_scalarMul_one :: forall a. TestableAbelianGroup a => TestTree
prop_scalarMul_one =
    testProperty
    (mkTestName @a "scalarMul_one") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (scalarMulP @a (integer 1) p) p
      pure $ evalTerm e === uplcTrue

prop_scalarMul_inverse :: forall a. TestableAbelianGroup a => TestTree
prop_scalarMul_inverse =
    testProperty
    (mkTestName @a "scalarMul_inverse") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (scalarMulP @a (integer (-1)) p) (negP @a p)
      pure $ evalTerm e == uplcTrue

prop_scalarMul_repeated_addition :: forall a. TestableAbelianGroup a => TestTree
prop_scalarMul_repeated_addition =
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

prop_scalarMul_periodic :: forall a. TestableAbelianGroup a => TestTree
prop_scalarMul_periodic =
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
         [ prop_scalarMul_assoc              @a
         , prop_scalarMul_distributive_left  @a
         , prop_scalarMul_distributive_right @a
         , prop_scalarMul_zero               @a
         , prop_scalarMul_one                @a
         , prop_scalarMul_inverse            @a
         , prop_scalarMul_repeated_addition  @a
         , prop_scalarMul_periodic           @a
         ]


---------------- Compression, uncompression, and hashing work properly ----------------

prop_roundtrip_compression :: forall e a. HashAndCompress e a => TestTree
prop_roundtrip_compression =
    testProperty
    (mkTestName @a "roundtrip_compression") .
    withNTests $ do
      p <- arbitraryConstant @a
      let e = eqP @a (uncompressP @e @a (compressP @e @a p)) p
      pure $ evalTerm e === uplcTrue

prop_uncompression_input_size :: forall e a. HashAndCompress e a => TestTree
prop_uncompression_input_size =
    testProperty
    (mkTestName @a "uncompression_input_size") .
    withNTests $ do
      b <- suchThat (resize 128 arbitrary) incorrectSize
      let e = uncompressP @e @a (bytestring b)
      pure $ evalTerm e === CekError
    where incorrectSize s =
              BS.length s /= compressedSize @e @a

prop_uncompress_out_of_group :: forall e a. HashAndCompress e a => TestTree
prop_uncompress_out_of_group =
    testProperty
    (mkTestName @a "uncompress_out_of_group") .
    withNTests $ do
      b <- resize (compressedSize @e @a) arbitrary
      let e = uncompressP @e @a (bytestring b)
      pure $ evalTerm e === CekError

prop_no_hash_collisions :: forall e a. HashAndCompress e a => TestTree
prop_no_hash_collisions =
    testProperty
    (mkTestName @a "no_hash_collisions") .
    withNTests $ do
      b1 <- arbitrary
      b2 <- arbitrary
      let e = eqP @a (hashToCurveP @e @a $ bytestring b1) (hashToCurveP @e @a $ bytestring b2)
      pure $ b1 /= b2 ==> evalTerm e === uplcFalse

test_compress_hash :: forall e a. HashAndCompress e a => TestTree
test_compress_hash =
    testGroup (printf "Uncompression and hashing behave properly for %s" $ gname @a)
         [ prop_roundtrip_compression    @e @a
         , prop_uncompression_input_size @e @a
         , prop_uncompress_out_of_group  @e @a
         , prop_no_hash_collisions       @e @a
         ]


---------------- Pairing properties ----------------

prop_pairing_left_additive :: TestTree
prop_pairing_left_additive =
    testProperty
    "pairing_left_additive" .
    withNTests $ do
      p1 <- arbitraryConstant @G1.Element
      p2 <- arbitraryConstant @G1.Element
      q  <- arbitraryConstant @G2.Element
      let e1 = pairingPlc (addP @G1.Element p1 p2) q
          e2 = mulMlResultPlc (pairingPlc p1 q) (pairingPlc p2 q)
          e3 = finalVerifyPlc e1 e2
      pure $ evalTerm e3 === uplcTrue

-- <p,q1+q2> = <p,q1>.<p,q2>
prop_pairing_right_additive :: TestTree
prop_pairing_right_additive =
    testProperty
    "pairing_right_additive" .
    withNTests $ do
      p  <- arbitraryConstant @G1.Element
      q1 <- arbitraryConstant @G2.Element
      q2 <- arbitraryConstant @G2.Element
      let e1 = pairingPlc p (addP @G2.Element q1 q2)
          e2 = mulMlResultPlc (pairingPlc p q1) (pairingPlc p q2)
          e3 = finalVerifyPlc e1 e2
      pure $ evalTerm e3 === uplcTrue

-- <[n]p,q> = <p,[n]q>
prop_pairing_balanced :: TestTree
prop_pairing_balanced =
     testProperty
     "pairing_balanced" .
     withNTests $ do
      n <- arbitraryScalar
      p <- arbitraryConstant @G1.Element
      q <- arbitraryConstant @G2.Element
      let e1 = pairingPlc (scalarMulP @G1.Element n p) q
          e2 = pairingPlc p (scalarMulP @G2.Element n q)
          e3 = finalVerifyPlc e1 e2
      pure $ evalTerm e3 === uplcTrue

prop_random_pairing :: TestTree
prop_random_pairing =
    testProperty
    "pairing_random_unequal" .
    withNTests $ do
       p1 <- arbitraryConstant @G1.Element
       p2 <- arbitraryConstant @G1.Element
       q1 <- arbitraryConstant @G2.Element
       q2 <- arbitraryConstant @G2.Element
       pure $ p1 /= p2 && q1 /= q2 ==>
            let e = finalVerifyPlc (pairingPlc p1 q1) (pairingPlc p2 q2)
            in evalTerm e === uplcFalse


-- All the tests

tests :: TestTree
tests = testGroup "*** Plutus property tests ***" [
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


