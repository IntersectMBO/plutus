-- editorconfig-checker-disable
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-dodgy-imports #-}

-- | Property tests for the BLS12-381 builtins
module Evaluation.Builtins.BLS12_381
where

import Evaluation.Builtins.BLS12_381.TestClasses
import Evaluation.Builtins.BLS12_381.Utils
import Evaluation.Builtins.Common
  ( PlcTerm
  , TypeErrorOrCekResult (..)
  , bytestring
  , cekSuccessFalse
  , cekSuccessTrue
  , evalTerm
  , integer
  , mkApp2
  )
import PlutusCore.Crypto.BLS12_381.Bounds qualified as Bounds
import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Default
import PlutusCore.Generators.QuickCheck.Builtin (arbitraryBuiltin)
import UntypedPlutusCore qualified as UPLC

import Cardano.Crypto.EllipticCurve.BLS12_381 (scalarPeriod)
import Control.Monad (replicateM)
import Data.ByteString as BS
  ( empty
  , length
  , pack
  )
import Data.List as List
  ( foldl'
  , genericReplicate
  , length
  , nub
  )
import Text.Printf (printf)

import Test.QuickCheck hiding (Some (..))
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Some (..))

import PlutusCore.MkPlc (mkConstant)

-- QuickCheck utilities

mkTestName :: forall g. TestableAbelianGroup g => String -> String
mkTestName s = printf "%s_%s" (groupName @g) s

withNTests :: Testable prop => prop -> Property
withNTests = withMaxSuccess 200

-- QuickCheck generators for scalars and group elements as PLC terms

-- Convert objects to terms, just for convenience.
asPlc :: DefaultUni `Contains` a => a -> PlcTerm
asPlc = mkConstant ()

{- Generate an arbitrary scalar.  Scalars map onto elements of Z_p where p is the
   255-bit prime order of the groups involved in BLS12_381.  This generator
   supplies integers up to 10000 bits long to give us some confidence that the
   reduction is handled properly.
-}
arbitraryScalar :: Gen Integer
arbitraryScalar =
  frequency
    [ (1, arbitraryBuiltin @Integer)
    , (4, choose (-b, b))
    ]
  where
    b = (2 :: Integer) ^ (10000 :: Integer)

-- Scalar inputs for the multiScalarMul functions, which enforce a bound.
arbitraryMsmScalar :: Gen Integer
arbitraryMsmScalar =
  frequency
    [ (1, arbitraryBuiltin @Integer `suchThat` (not . Bounds.msmScalarOutOfBounds))
    , (4, choose (Bounds.msmScalarLb, Bounds.msmScalarUb))
    ]

-- Arbitrary scalar as PLC constant
arbitraryPlcScalar :: Gen PlcTerm
arbitraryPlcScalar = asPlc <$> arbitraryScalar

-- Arbitrary group element as PLC constant
arbitraryPlcConst :: forall g. (DefaultUni `Contains` g, Arbitrary g) => Gen PlcTerm
arbitraryPlcConst = asPlc <$> arbitrary @g

-- Arbitrary nonzero group element as PLC constant
arbitraryNonZeroPlcConst :: forall g. TestableAbelianGroup g => Gen PlcTerm
arbitraryNonZeroPlcConst = asPlc <$> arbitraryNonZero @g

{- Generic tests for the TestableAbelianGroup class.  Later these are instantiated
   at the G1 and G2 types. -}

---------------- G is an Abelian group ----------------

-- | Group addition is associative.
test_add_assoc :: forall g. TestableAbelianGroup g => TestTree
test_add_assoc =
  testProperty
    (mkTestName @g "add_assoc")
    . withNTests
    $ do
      p1 <- arbitraryPlcConst @g
      p2 <- arbitraryPlcConst @g
      p3 <- arbitraryPlcConst @g
      let e = eqTerm @g (addTerm @g p1 (addTerm @g p2 p3)) (addTerm @g (addTerm @g p1 p2) p3)
      pure $ evalTerm e === cekSuccessTrue

-- | Zero is an identity for addition.
test_add_zero :: forall g. TestableAbelianGroup g => TestTree
test_add_zero =
  testProperty
    (mkTestName @g "add_zero")
    . withNTests
    $ do
      p <- arbitraryPlcConst @g
      let e = eqTerm @g (addTerm @g p $ zeroTerm @g) p
      pure $ evalTerm e === cekSuccessTrue

{-| Every element has an inverse
| a+(-a) = 0 for all group elements. -}
test_neg :: forall g. TestableAbelianGroup g => TestTree
test_neg =
  testProperty
    (mkTestName @g "additive_inverse")
    . withNTests
    $ do
      p <- arbitraryPlcConst @g
      let e = eqTerm @g (addTerm @g p (negTerm @g p)) $ zeroTerm @g
      pure $ evalTerm e === cekSuccessTrue

-- | Group addition is commutative.
test_add_commutative :: forall g. TestableAbelianGroup g => TestTree
test_add_commutative =
  testProperty
    (mkTestName @g "add_commutative")
    . withNTests
    $ do
      p1 <- arbitraryPlcConst @g
      p2 <- arbitraryPlcConst @g
      let e = eqTerm @g (addTerm @g p1 p2) (addTerm @g p2 p1)
      pure $ evalTerm e === cekSuccessTrue

test_is_an_abelian_group :: forall g. TestableAbelianGroup g => TestTree
test_is_an_abelian_group =
  testGroup
    (mkTestName @g "is_an_abelian_group")
    [ test_add_assoc @g
    , test_add_zero @g
    , test_neg @g
    , test_add_commutative @g
    ]

---------------- Z acts on G correctly ----------------

-- | (ab)p = a(bp) for all scalars a and b and all group elements p.
test_scalarMul_assoc :: forall g. TestableAbelianGroup g => TestTree
test_scalarMul_assoc =
  testProperty
    (mkTestName @g "scalarMul_mul_assoc")
    . withNTests
    $ do
      m <- arbitraryPlcScalar
      n <- arbitraryPlcScalar
      p <- arbitraryPlcConst @g
      let e1 = scalarMulTerm @g (mkApp2 MultiplyInteger m n) p
          e2 = scalarMulTerm @g m (scalarMulTerm @g n p)
          e3 = eqTerm @g e1 e2
      pure $ evalTerm e3 === cekSuccessTrue

-- | (a+b)p = ap +bp for all scalars a and b and all group elements p.
test_scalarMul_distributive_left :: forall g. TestableAbelianGroup g => TestTree
test_scalarMul_distributive_left =
  testProperty
    (mkTestName @g "scalarMul_distributive_left")
    . withNTests
    $ do
      m <- arbitraryPlcScalar
      n <- arbitraryPlcScalar
      p <- arbitraryPlcConst @g
      let e1 = scalarMulTerm @g (mkApp2 AddInteger m n) p
          e2 = addTerm @g (scalarMulTerm @g m p) (scalarMulTerm @g n p)
          e3 = eqTerm @g e1 e2
      pure $ evalTerm e3 === cekSuccessTrue

-- | a(p+q) = ap + aq for all scalars a and all group elements p and q.
test_scalarMul_distributive_right :: forall g. TestableAbelianGroup g => TestTree
test_scalarMul_distributive_right =
  testProperty
    (mkTestName @g "scalarMul_distributive_right")
    . withNTests
    $ do
      n <- arbitraryPlcScalar
      p <- arbitraryPlcConst @g
      q <- arbitraryPlcConst @g
      let e1 = scalarMulTerm @g n (addTerm @g p q)
          e2 = addTerm @g (scalarMulTerm @g n p) (scalarMulTerm @g n q)
          e3 = eqTerm @g e1 e2
      pure $ evalTerm e3 === cekSuccessTrue

-- | 0p = 0 for all group elements p.
test_scalarMul_zero :: forall g. TestableAbelianGroup g => TestTree
test_scalarMul_zero =
  testProperty
    (mkTestName @g "scalarMul_zero")
    . withNTests
    $ do
      p <- arbitraryPlcConst @g
      let e = eqTerm @g (scalarMulTerm @g (integer 0) p) $ zeroTerm @g
      pure $ evalTerm e === cekSuccessTrue

-- | 1p = p for all group elements p.
test_scalarMul_one :: forall g. TestableAbelianGroup g => TestTree
test_scalarMul_one =
  testProperty
    (mkTestName @g "scalarMul_one")
    . withNTests
    $ do
      p <- arbitraryPlcConst @g
      let e = eqTerm @g (scalarMulTerm @g (integer 1) p) p
      pure $ evalTerm e === cekSuccessTrue

-- | (-1)p = -p for all group elements p.
test_scalarMul_inverse :: forall g. TestableAbelianGroup g => TestTree
test_scalarMul_inverse =
  testProperty
    (mkTestName @g "scalarMul_inverse")
    . withNTests
    $ do
      p <- arbitraryPlcConst @g
      let e = eqTerm @g (scalarMulTerm @g (integer (-1)) p) (negTerm @g p)
      pure $ evalTerm e == cekSuccessTrue

-- Check that scalar multiplication is repeated addition (including negative
-- scalars). We should really check this for scalars greater than the group
-- order, but that would be prohibitively slow because the order of G1 and G2
-- has 256 bits (about 5*10^76).
test_scalarMul_repeated_addition :: forall g. TestableAbelianGroup g => TestTree
test_scalarMul_repeated_addition =
  testProperty
    (mkTestName @g "scalarMul_repeated_addition")
    . withNTests
    $ do
      n <- resize 100 arbitrary -- number of additions
      p <- arbitraryPlcConst @g
      let e1 = repeatedAdd n p
          e2 = eqTerm @g (scalarMulTerm @g (integer n) p) e1
      pure $ evalTerm e2 === cekSuccessTrue
  where
    repeatedAdd :: Integer -> PlcTerm -> PlcTerm
    repeatedAdd n t =
      if n >= 0
        then List.foldl' (addTerm @g) (zeroTerm @g) $ genericReplicate n t
        else repeatedAdd (-n) (negTerm @g t)

-- (m + n|G|)p = mp for all group elements p and integers m and n.
-- We have |G1| = |G2| = scalarPeriod
test_scalarMul_periodic :: forall g. TestableAbelianGroup g => TestTree
test_scalarMul_periodic =
  testProperty
    (mkTestName @g "scalarMul_periodic")
    . withNTests
    $ do
      m <- arbitraryPlcScalar
      n <- arbitraryPlcScalar
      p <- arbitraryPlcConst @g
      let e1 = scalarMulTerm @g m p
          k = mkApp2 AddInteger m (mkApp2 MultiplyInteger n (integer scalarPeriod))
          e2 = scalarMulTerm @g k p -- k = m+n|G|
          e = eqTerm @g e1 e2
      pure $ evalTerm e === cekSuccessTrue

test_Z_action_good :: forall g. TestableAbelianGroup g => TestTree
test_Z_action_good =
  testGroup
    (printf "Z acts correctly on %s" $ groupName @g)
    [ test_scalarMul_assoc @g
    , test_scalarMul_distributive_left @g
    , test_scalarMul_distributive_right @g
    , test_scalarMul_zero @g
    , test_scalarMul_one @g
    , test_scalarMul_inverse @g
    , test_scalarMul_repeated_addition @g
    , test_scalarMul_periodic @g
    ]

---------------- Multi-scalar multiplication behaves correctly ----------------

{- Check that multiScalarMul [s_1, ..., s_m] [p_1, ..., p_n] =
      0 + (s_1*p_1) + ... + (s_r*p_r) where r = min m n
-}
test_multiScalarMul_correct :: forall g. TestableAbelianGroup g => TestTree
test_multiScalarMul_correct =
  testProperty
    (mkTestName @g "multiScalarMul_is_iterated_mul_and_add")
    . withNTests
    $ do
      scalars <- listOf arbitraryMsmScalar
      points <- listOf (arbitrary @g)
      let e1 = multiScalarMulTerm @g (asPlc scalars) (asPlc points)
          mkMulAdd acc (s, x) = addTerm @g acc (scalarMulTerm @g s x)
          scalarTerms = fmap asPlc scalars
          pointTerms = fmap asPlc points
          e2 = List.foldl' mkMulAdd (zeroTerm @g) (zip scalarTerms pointTerms)
      -- \^ Remember that zip truncates the longer list and `multiScalarMul`
      -- is supposed to disregard extra elements if the inputs have different
      -- lengths.
      pure $ evalTerm e1 === evalTerm e2

-- Check that multiScalarMul returns the zero point if the list of scalars is empty
test_multiScalarMul_no_scalars :: forall g. TestableAbelianGroup g => TestTree
test_multiScalarMul_no_scalars =
  testProperty
    (mkTestName @g "multiScalarMul_returns_zero_if_no_scalars")
    . withNTests
    $ do
      points <- listOf (arbitrary @g)
      let e = multiScalarMulTerm @g (asPlc ([] @Integer)) (asPlc points)
      pure $ evalTerm e === evalTerm (zeroTerm @g)

-- Check that multiScalarMul returns the zero point if the list of points is empty
test_multiScalarMul_no_points :: forall g. TestableAbelianGroup g => TestTree
test_multiScalarMul_no_points =
  testProperty
    (mkTestName @g "multiScalarMul_returns_zero_if_no_points")
    . withNTests
    $ do
      scalars <- listOf arbitraryMsmScalar
      let e = multiScalarMulTerm @g (asPlc scalars) (asPlc ([] @g))
      pure $ evalTerm e === evalTerm (zeroTerm @g)

{- Check that the result of multiScalarMul doesn't change if you permute the input
   pairs (disregarding extra inputs when the two input lists are of different
   lengths).
-}
test_multiScalarMul_permutation :: forall g. TestableAbelianGroup g => TestTree
test_multiScalarMul_permutation =
  testProperty
    (mkTestName @g "multiScalarMul_invariant_under_permutation")
    . withNTests
    $ do
      l <- listOf ((,) <$> arbitraryMsmScalar <*> arbitrary @g)
      l' <- shuffle l
      let (scalars, points) = unzip l
          (scalars', points') = unzip l'
          e1 = multiScalarMulTerm @g (asPlc scalars) (asPlc points)
          e2 = multiScalarMulTerm @g (asPlc scalars') (asPlc points')
      pure $ evalTerm e1 === evalTerm e2

test_multiScalarMul :: forall g. TestableAbelianGroup g => TestTree
test_multiScalarMul =
  testGroup
    (printf "Multi-scalar multiplication behaves correctly for %s" $ groupName @g)
    [ test_multiScalarMul_correct @g
    , test_multiScalarMul_no_scalars @g
    , test_multiScalarMul_no_points @g
    , test_multiScalarMul_permutation @g
    ]

{- Generic tests for the HashAndCompress class.  Later these are instantiated at
   the G1 and G2 types. -}

test_roundtrip_compression :: forall g. HashAndCompress g => TestTree
test_roundtrip_compression =
  testProperty
    (mkTestName @g "roundtrip_compression")
    . withNTests
    $ do
      p <- arbitraryPlcConst @g
      let e = eqTerm @g (uncompressTerm @g (compressTerm @g p)) p
      pure $ evalTerm e === cekSuccessTrue

{-| Uncompression should only accept inputs of the expected length, so we check
it on random inputs of the incorrect length.  Inputs of the expected length
are excluded by the incorrectSize predicate; however even if an input did
have the expected length it would be very unlikely to deserialise to a point
in the group because the cofactors are very big (7.6*10^37 for G1 and
3.1*10^152 for G2). -}
test_uncompression_wrong_size :: forall g. HashAndCompress g => TestTree
test_uncompression_wrong_size =
  testProperty
    (mkTestName @g "uncompression_wrong_size")
    . withNTests
    $ do
      b <- suchThat (resize 128 arbitrary) incorrectSize
      let e = uncompressTerm @g (bytestring b)
      pure $ evalTerm e === CekError
  where
    incorrectSize s = BS.length s /= compressedSize @g

{-| This tests the case we've omitted in the previous test, and should fail
with very high probablity.  It's quite difficult to test this with random
inputs.  We can improve our chances of getting a bytestring which encodes a
point on the curve by setting the compression bit and clearing the infinity
bit, but about 50% of the samples will still not be the x-coordinate of a
point on the curve.  We can also generate points with an x-coordinate that's
bigger than the field size (especially for G2), which will give us a bad
encoding.  Maybe this just isn't a very good test. -}
test_uncompress_out_of_group :: forall g. HashAndCompress g => TestTree
test_uncompress_out_of_group =
  testProperty
    (mkTestName @g "uncompress_out_of_group")
    . withMaxSuccess 99
    $ do
      b <- suchThat (resize 128 arbitrary) correctSize
      let b' = setBits compressionBit $ clearBits infinityBit b
      let e = uncompressTerm @g (bytestring b')
      pure $ evalTerm e === CekError
  where
    correctSize s = BS.length s == compressedSize @g

-- | Check that the most significant bit is set for all compressed points
test_compression_bit_set :: forall g. HashAndCompress g => TestTree
test_compression_bit_set =
  testProperty
    (mkTestName @g "compression_bit_set")
    . withNTests
    $ do
      p <- arbitraryPlcConst @g
      case evalTerm (compressTerm @g p) of
        CekSuccess (UPLC.Constant _ (Some (ValueOf DefaultUniByteString bs))) ->
          pure $ isSet compressionBit bs
        _ -> pure False

-- | Check that bytestrings with the compression bit clear fail to uncompress.
test_clear_compression_bit :: forall g. HashAndCompress g => TestTree
test_clear_compression_bit =
  testProperty
    (mkTestName @g "clear_compression_bit")
    . withNTests
    $ do
      p <- arbitrary @g
      let b = clearBits compressionBit $ compress @g p
          e = uncompressTerm @g (bytestring b)
      pure $ evalTerm e === CekError

{-| Check that flipping the sign bit in a compressed nonzero point gives the
inverse of the point. -}
test_flip_sign_bit :: forall g. HashAndCompress g => TestTree
test_flip_sign_bit =
  testProperty
    (mkTestName @g "flip_sign_bit")
    . withNTests
    $ do
      p <- arbitraryNonZero @g
      let b1 = compress @g p
          b2 = flipBits signBit b1
          e1 = uncompressTerm @g (bytestring b1)
          e2 = uncompressTerm @g (bytestring b2)
          e = eqTerm @g e2 (negTerm @g e1)
      pure $ evalTerm e === cekSuccessTrue

-- | Check that bytestrings with the infinity bit set fail to uncompress.
test_set_infinity_bit :: forall g. HashAndCompress g => TestTree
test_set_infinity_bit =
  testProperty
    (mkTestName @g "set_infinity_bit")
    . withNTests
    $ do
      p <- arbitraryNonZero @g -- This will have the infinity bit set.
      let b = setBits infinityBit $ compress @g p
          e = uncompressTerm @g (bytestring b)
      pure $ evalTerm e === CekError

-- We test for hash collisions by generating a list of `numHashCollisionTests`
-- bytestrings, discarding duplicates, hashing the remaining bytestrings, and
-- then checking that no two of the resulting group elements are equal. The time
-- taken by the tests increases quadratically with the number of bytestrings,
-- and is quite long even for numHashCollisionTests = 50.
numHashCollisionInputs :: Int
numHashCollisionInputs = 200

{-| Hashing into G1 or G2 should be collision-free.  A failure here would
suggest an implementation error somewhere.  Here we test multiple messages
but always use an empty Domain Separation Tag. -}
test_no_hash_collisions :: forall g. HashAndCompress g => TestTree
test_no_hash_collisions =
  let emptyBS = bytestring BS.empty
   in testProperty
        (mkTestName @g "no_hash_collisions")
        . withMaxSuccess 1
        $ do
          msgs <- nub <$> replicateM numHashCollisionInputs arbitrary
          let terms = fmap (\msg -> hashToGroupTerm @g (bytestring msg) emptyBS) msgs
              hashed = fmap evalTerm terms
              noErrors = property $ all (/= CekError) hashed -- Just in case
              noDuplicates = List.length hashed === List.length (nub hashed)
          pure $ noErrors .&. noDuplicates

{-| Test that we get no collisions if we keep the message constant but vary the
DST.  DSTs can be at most 255 bytes long in Plutus Core; there's a test
elsewhere that we get a failure for longer DSTs.  This test could fail (but
not because of a hash collision) if we let it generate longer DSTs because
the final list could contain multiple occurrences of CekError. -}
test_no_hash_collisions_dst :: forall g. HashAndCompress g => TestTree
test_no_hash_collisions_dst =
  let msg = bytestring $ pack [0x01, 0x02]
      maxDstSize = 255
   in testProperty
        (mkTestName @g "no_hash_collisions_dst")
        . withMaxSuccess 1
        $ do
          dsts <- nub <$> replicateM numHashCollisionInputs (resize maxDstSize arbitrary)
          let terms = fmap (\dst -> hashToGroupTerm @g msg (bytestring dst)) dsts
              hashed = fmap evalTerm terms
              noErrors = property $ all (/= CekError) hashed
              noDuplicates = List.length hashed === List.length (nub hashed)
          pure $ noErrors .&. noDuplicates

test_compress_hash :: forall g. HashAndCompress g => TestTree
test_compress_hash =
  testGroup
    (printf "Uncompression and hashing behave properly for %s" $ groupName @g)
    [ test_roundtrip_compression @g
    , test_uncompression_wrong_size @g
    , test_compression_bit_set @g
    , test_clear_compression_bit @g
    , test_flip_sign_bit @g
    , test_set_infinity_bit @g
    , test_uncompress_out_of_group @g
    , test_no_hash_collisions @g
    , test_no_hash_collisions_dst @g
    ]

---------------- Pairing properties ----------------

-- Constructing pairing terms

millerLoopTerm :: PlcTerm -> PlcTerm -> PlcTerm
millerLoopTerm = mkApp2 Bls12_381_millerLoop

mulMlResultTerm :: PlcTerm -> PlcTerm -> PlcTerm
mulMlResultTerm = mkApp2 Bls12_381_mulMlResult

finalVerifyTerm :: PlcTerm -> PlcTerm -> PlcTerm
finalVerifyTerm = mkApp2 Bls12_381_finalVerify

-- <p1+p2,q> = <p1,q>.<p2,q>
test_pairing_left_additive :: TestTree
test_pairing_left_additive =
  testProperty
    "pairing_left_additive"
    . withNTests
    $ do
      p1 <- arbitraryPlcConst @G1.Element
      p2 <- arbitraryPlcConst @G1.Element
      q <- arbitraryPlcConst @G2.Element
      let e1 = millerLoopTerm (addTerm @G1.Element p1 p2) q
          e2 = mulMlResultTerm (millerLoopTerm p1 q) (millerLoopTerm p2 q)
          e3 = finalVerifyTerm e1 e2
      pure $ evalTerm e3 === cekSuccessTrue

-- <p,q1+q2> = <p,q1>.<p,q2>
test_pairing_right_additive :: TestTree
test_pairing_right_additive =
  testProperty
    "pairing_right_additive"
    . withNTests
    $ do
      p <- arbitraryPlcConst @G1.Element
      q1 <- arbitraryPlcConst @G2.Element
      q2 <- arbitraryPlcConst @G2.Element
      let e1 = millerLoopTerm p (addTerm @G2.Element q1 q2)
          e2 = mulMlResultTerm (millerLoopTerm p q1) (millerLoopTerm p q2)
          e3 = finalVerifyTerm e1 e2
      pure $ evalTerm e3 === cekSuccessTrue

-- <[n]p,q> = <p,[n]q>
test_pairing_balanced :: TestTree
test_pairing_balanced =
  testProperty
    "pairing_balanced"
    . withNTests
    $ do
      n <- arbitraryPlcScalar
      p <- arbitraryPlcConst @G1.Element
      q <- arbitraryPlcConst @G2.Element
      let e1 = millerLoopTerm (scalarMulTerm @G1.Element n p) q
          e2 = millerLoopTerm p (scalarMulTerm @G2.Element n q)
          e3 = finalVerifyTerm e1 e2
      pure $ evalTerm e3 === cekSuccessTrue

-- Check that `finalVerify` returns False for random inputs.  We exclude the
-- zero points because `millerLoop` returns 1 if either of its inputs is zero.
test_random_pairing :: TestTree
test_random_pairing =
  testProperty
    "pairing_random_unequal"
    . withNTests
    $ do
      p1 <- arbitraryNonZeroPlcConst @G1.Element
      p2 <- arbitraryNonZeroPlcConst @G1.Element
      q1 <- arbitraryNonZeroPlcConst @G2.Element
      q2 <- arbitraryNonZeroPlcConst @G2.Element
      pure $
        p1 /= p2 && q1 /= q2 ==>
          let e = finalVerifyTerm (millerLoopTerm p1 q1) (millerLoopTerm p2 q2)
           in evalTerm e === cekSuccessFalse

-- All of the tests

test_BLS12_381 :: TestTree
test_BLS12_381 =
  testGroup
    "BLS12-381"
    [ testGroup
        "G1 properties"
        [ test_is_an_abelian_group @G1.Element
        , test_Z_action_good @G1.Element
        , test_multiScalarMul @G1.Element
        , test_compress_hash @G1.Element
        ]
    , testGroup
        "G2 properties"
        [ test_is_an_abelian_group @G2.Element
        , test_Z_action_good @G2.Element
        , test_multiScalarMul @G2.Element
        , test_compress_hash @G2.Element
        ]
    , testGroup
        "Pairing properties"
        [ test_pairing_left_additive
        , test_pairing_right_additive
        , test_pairing_balanced
        , test_random_pairing
        ]
    ]
