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

import Evaluation.Builtins.BLS12_381.Conformance
import Evaluation.Builtins.BLS12_381.TestClasses
import Evaluation.Builtins.BLS12_381.Utils
import Evaluation.Builtins.Common
  ( PlcTerm
  , TypeErrorOrCekResult (CekError)
  , bytestring
  , cekSuccessFalse
  , cekSuccessTrue
  , integer
  , mkApp2
  )
import Evaluation.Builtins.Conformance
  ( Check (..)
  , CheckMode
  , OutputFormat
  , PropertyFilter
  , PropertyId (..)
  , PropertyReport (..)
  , PropertySpec (..)
  , checkUniqueIds
  )
import PlutusCore.Crypto.BLS12_381.Bounds qualified as Bounds
import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Default
import PlutusCore.Generators.QuickCheck.Builtin (arbitraryBuiltin)

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
  , nub
  )
import Data.Maybe (catMaybes, fromMaybe)
import Test.QuickCheck.Random (QCGen)
import Text.Printf (printf)

import Test.Cardano.Base.QuickCheck qualified as BaseQC
import Test.QuickCheck hiding (Some (..))
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Some (..))

import PlutusCore.MkPlc (mkConstant)

-- QuickCheck utilities

mkTestName :: forall g. TestableAbelianGroup g => String -> String
mkTestName s = printf "%s_%s" (groupName @g) s

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
    b = (2 :: Integer) ^ (2047 :: Integer)

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

---------------- Property specifications ----------------

{- Properties shared by the normal test suite and the conformance test
generator.  Identifiers are the stable test case names; descriptions are what
the test runner displays.  The subgroup lists are instantiated for both G1 and G2
by 'groupProperties'. -}
-- | The group axioms.
abelianGroupProperties :: forall g. TestableAbelianGroup g => [PropertySpec (Gen Check)]
abelianGroupProperties =
  [ -- Group addition is associative.
    PropertySpec "add_assoc" (mkTestName @g "add_assoc") (cases_add_assoc @g)
  , -- Zero is an identity for addition.
    PropertySpec "add_zero" (mkTestName @g "add_zero") (cases_add_zero @g)
  , -- Every element has an inverse: a + (-a) = 0.
    PropertySpec "neg" (mkTestName @g "additive_inverse") (cases_neg @g)
  , -- Group addition is commutative.
    PropertySpec "add_commutative" (mkTestName @g "add_commutative") (cases_add_commutative @g)
  ]

-- | The integers act on the group.
zActionProperties :: forall g. TestableAbelianGroup g => [PropertySpec (Gen Check)]
zActionProperties =
  [ -- (ab)p = a(bp).
    PropertySpec
      "scalarMul_assoc"
      (mkTestName @g "scalarMul_mul_assoc")
      (cases_scalarMul_assoc @g)
  , -- (a+b)p = ap + bp.
    PropertySpec
      "scalarMul_left_distributive"
      (mkTestName @g "scalarMul_left_distributive")
      (cases_scalarMul_left_distributive @g)
  , -- a(p+q) = ap + aq.
    PropertySpec
      "scalarMul_right_distributive"
      (mkTestName @g "scalarMul_right_distributive")
      (cases_scalarMul_right_distributive @g)
  , -- 0p = 0.
    PropertySpec "scalarMul_zero" (mkTestName @g "scalarMul_zero") (cases_scalarMul_zero @g)
  , -- 1p = p.
    PropertySpec "scalarMul_one" (mkTestName @g "scalarMul_one") (cases_scalarMul_one @g)
  , -- (-1)p = -p.
    PropertySpec "scalarMul_inverse" (mkTestName @g "scalarMul_inverse") (cases_scalarMul_inverse @g)
  , -- Scalar multiplication is repeated addition, including negative scalars.
    -- We should really check this for scalars greater than the group order, but
    -- that would be prohibitively slow because the order of G1 and G2 has 256
    -- bits (about 5*10^76).
    PropertySpec
      "scalarMul_repeated_addition"
      (mkTestName @g "scalarMul_repeated_addition")
      (cases_scalarMul_repeated_addition @g)
  , -- (m + n|G|)p = mp, where |G1| = |G2| = scalarPeriod.
    PropertySpec
      "scalarMul_periodic"
      (mkTestName @g "scalarMul_periodic")
      (cases_scalarMul_periodic @g)
  ]

-- | Multi-scalar multiplication.
multiScalarMulProperties :: forall g. TestableAbelianGroup g => [PropertySpec (Gen Check)]
multiScalarMulProperties =
  [ -- multiScalarMul [s_1, ..., s_m] [p_1, ..., p_n] =
    -- 0 + (s_1*p_1) + ... + (s_r*p_r) where r = min m n.
    PropertySpec
      "multiScalarMul_correct"
      (mkTestName @g "multiScalarMul_is_iterated_mul_and_add")
      (cases_multiScalarMul_correct @g)
  , -- multiScalarMul returns the zero point if the list of scalars is empty.
    PropertySpec
      "multiScalarMul_no_scalars"
      (mkTestName @g "multiScalarMul_returns_zero_if_no_scalars")
      (cases_multiScalarMul_no_scalars @g)
  , -- multiScalarMul returns the zero point if the list of points is empty.
    PropertySpec
      "multiScalarMul_no_points"
      (mkTestName @g "multiScalarMul_returns_zero_if_no_points")
      (cases_multiScalarMul_no_points @g)
  , -- The result doesn't change if the input pairs are permuted (disregarding
    -- extra inputs when the two input lists have different lengths).
    PropertySpec
      "multiScalarMul_permutation"
      (mkTestName @g "multiScalarMul_invariant_under_permutation")
      (cases_multiScalarMul_permutation @g)
  ]

-- | Uncompression and hashing.
compressHashProperties :: forall g. HashAndCompress g => [PropertySpec (Gen Check)]
compressHashProperties =
  [ PropertySpec
      "roundtrip_compression"
      (mkTestName @g "roundtrip_compression")
      (cases_roundtrip_compression @g)
  , -- Uncompression should only accept inputs of the expected length, so we
    -- check it on random inputs of the incorrect length.  Inputs of the expected
    -- length are excluded by the incorrectSize predicate; however even if an
    -- input did have the expected length it would be very unlikely to
    -- deserialise to a point in the group because the cofactors are very big
    -- (7.6*10^37 for G1 and 3.1*10^152 for G2).
    PropertySpec
      "uncompression_wrong_size"
      (mkTestName @g "uncompression_wrong_size")
      (cases_uncompression_wrong_size @g)
  , -- Check that the most significant bit is set for all compressed points.
    PropertySpec
      "compression_bit_set"
      (mkTestName @g "compression_bit_set")
      (cases_compression_bit_set @g)
  , -- Bytestrings with the compression bit clear fail to uncompress.
    PropertySpec
      "clear_compression_bit"
      (mkTestName @g "clear_compression_bit")
      (cases_clear_compression_bit @g)
  , -- Flipping the sign bit in a compressed nonzero point gives its inverse.
    PropertySpec
      "flip_sign_bit"
      (mkTestName @g "flip_sign_bit")
      (cases_flip_sign_bit @g)
  , -- Bytestrings with the infinity bit set fail to uncompress.
    PropertySpec
      "set_infinity_bit"
      (mkTestName @g "set_infinity_bit")
      (cases_set_infinity_bit @g)
  , -- This tests the case omitted by uncompression_wrong_size, and should fail
    -- with very high probablity.  It's quite difficult to test this with random
    -- inputs.  We can improve our chances of getting a bytestring which encodes a
    -- point on the curve by setting the compression bit and clearing the infinity
    -- bit, but about 50% of the samples will still not be the x-coordinate of a
    -- point on the curve.  We can also generate points with an x-coordinate that's
    -- bigger than the field size (especially for G2), which will give us a bad
    -- encoding.  Maybe this just isn't a very good test.
    PropertySpec
      "uncompress_out_of_group"
      (mkTestName @g "uncompress_out_of_group")
      (cases_uncompress_out_of_group @g)
  , -- Hashing into G1 or G2 should be collision-free, using an empty DST.
    PropertySpec
      "no_hash_collisions"
      (mkTestName @g "no_hash_collisions")
      (cases_no_hash_collisions @g)
  , -- No collisions when the message is fixed but the DST varies.  DSTs can be at
    -- most 255 bytes long in Plutus Core; longer ones fail elsewhere.  This could
    -- fail (not because of a collision) if DSTs were allowed to grow, because the
    -- list could then contain multiple CekErrors.
    PropertySpec
      "no_hash_collisions_dst"
      (mkTestName @g "no_hash_collisions_dst")
      (cases_no_hash_collisions_dst @g)
  ]

-- | Pairing properties, which don't depend on the group parameter.
pairingProperties :: [PropertySpec (Gen Check)]
pairingProperties =
  [ -- <p1+p2,q> = <p1,q>.<p2,q>
    PropertySpec "pairing_left_additive" "pairing_left_additive" cases_pairing_left_additive
  , -- <p,q1+q2> = <p,q1>.<p,q2>
    PropertySpec "pairing_right_additive" "pairing_right_additive" cases_pairing_right_additive
  , -- <[n]p,q> = <p,[n]q>
    PropertySpec "pairing_balanced" "pairing_balanced" cases_pairing_balanced
  , -- finalVerify returns False for random inputs.  Zero points are excluded
    -- because millerLoop returns 1 if either input is zero.
    PropertySpec "random_pairing" "pairing_random_unequal" cases_random_pairing
  ]

-- | The properties of one group, grouped as they appear in the test tree.
groupProperties
  :: forall g. HashAndCompress g => [(TestName, [PropertySpec (Gen Check)])]
groupProperties =
  [ (mkTestName @g "is_an_abelian_group", abelianGroupProperties @g)
  , (printf "Z acts correctly on %s" $ groupName @g, zActionProperties @g)
  ,
    ( printf "Multi-scalar multiplication behaves correctly for %s" $ groupName @g
    , multiScalarMulProperties @g
    )
  ,
    ( printf "Uncompression and hashing behave properly for %s" $ groupName @g
    , compressHashProperties @g
    )
  ]

---------------- Test tree ----------------

test_BLS12_381 :: TestTree
test_BLS12_381 =
  testGroup
    "BLS12-381"
    [ test_override_ids
    , testGroup "G1 properties" (map (uncurry testSubgroup) (groupProperties @G1.Element))
    , testGroup "G2 properties" (map (uncurry testSubgroup) (groupProperties @G2.Element))
    , testGroup "Pairing properties" (map testSpec pairingProperties)
    ]

-- | Guard against renaming a property and silently losing its test limit.
test_override_ids :: TestTree
test_override_ids =
  testProperty "test limits refer to existing properties" $
    BaseQC.withNumTests 1 $
      property $
        all (`elem` allPropertyIds) (map fst overriddenTests)
  where
    allPropertyIds =
      map propertySpecId (concatMap snd $ groupProperties @G1.Element)
        <> map propertySpecId (concatMap snd $ groupProperties @G2.Element)
        <> map propertySpecId pairingProperties

testSubgroup :: TestName -> [PropertySpec (Gen Check)] -> TestTree
testSubgroup name = testGroup name . map testSpec

testSpec :: PropertySpec (Gen Check) -> TestTree
testSpec spec =
  testProperty (propertySpecDescription spec) $
    BaseQC.withNumTests
      (numberOfTests (propertySpecId spec))
      (property (propertySpecCheck spec))

-- | QuickCheck's default number of cases for a property.
defaultTests :: Int
defaultTests = 200

{-| Properties that run fewer cases than the default: hashing is quadratic in
the number of inputs and random uncompression is slow. -}
overriddenTests :: [(String, Int)]
overriddenTests =
  [ ("uncompress_out_of_group", 99)
  , ("no_hash_collisions", 1)
  , ("no_hash_collisions_dst", 1)
  ]

numberOfTests :: String -> Int
numberOfTests identifier = fromMaybe defaultTests (lookup identifier overriddenTests)

-- Shared input generators and unevaluated checks.

---------------- Abelian group properties ----------------

cases_add_assoc :: forall g. TestableAbelianGroup g => Gen Check
cases_add_assoc = do
  p1 <- arbitraryPlcConst @g
  p2 <- arbitraryPlcConst @g
  p3 <- arbitraryPlcConst @g
  let e = eqTerm @g (addTerm @g p1 (addTerm @g p2 p3)) (addTerm @g (addTerm @g p1 p2) p3)
  pure $ CheckEvaluatesTo e cekSuccessTrue

cases_add_zero :: forall g. TestableAbelianGroup g => Gen Check
cases_add_zero = do
  p <- arbitraryPlcConst @g
  let e = eqTerm @g (addTerm @g p $ zeroTerm @g) p
  pure $ CheckEvaluatesTo e cekSuccessTrue

cases_neg :: forall g. TestableAbelianGroup g => Gen Check
cases_neg = do
  p <- arbitraryPlcConst @g
  let e = eqTerm @g (addTerm @g p (negTerm @g p)) $ zeroTerm @g
  pure $ CheckEvaluatesTo e cekSuccessTrue

cases_add_commutative :: forall g. TestableAbelianGroup g => Gen Check
cases_add_commutative = do
  p1 <- arbitraryPlcConst @g
  p2 <- arbitraryPlcConst @g
  let e = eqTerm @g (addTerm @g p1 p2) (addTerm @g p2 p1)
  pure $ CheckEvaluatesTo e cekSuccessTrue

---------------- Z action properties ----------------

cases_scalarMul_assoc :: forall g. TestableAbelianGroup g => Gen Check
cases_scalarMul_assoc = do
  m <- arbitraryPlcScalar
  n <- arbitraryPlcScalar
  p <- arbitraryPlcConst @g
  let e1 = scalarMulTerm @g (mkApp2 MultiplyInteger m n) p
      e2 = scalarMulTerm @g m (scalarMulTerm @g n p)
      e3 = eqTerm @g e1 e2
  pure $ CheckEvaluatesTo e3 cekSuccessTrue

cases_scalarMul_left_distributive :: forall g. TestableAbelianGroup g => Gen Check
cases_scalarMul_left_distributive = do
  m <- arbitraryPlcScalar
  n <- arbitraryPlcScalar
  p <- arbitraryPlcConst @g
  let e1 = scalarMulTerm @g (mkApp2 AddInteger m n) p
      e2 = addTerm @g (scalarMulTerm @g m p) (scalarMulTerm @g n p)
      e3 = eqTerm @g e1 e2
  pure $ CheckEvaluatesTo e3 cekSuccessTrue

cases_scalarMul_right_distributive :: forall g. TestableAbelianGroup g => Gen Check
cases_scalarMul_right_distributive = do
  n <- arbitraryPlcScalar
  p <- arbitraryPlcConst @g
  q <- arbitraryPlcConst @g
  let e1 = scalarMulTerm @g n (addTerm @g p q)
      e2 = addTerm @g (scalarMulTerm @g n p) (scalarMulTerm @g n q)
      e3 = eqTerm @g e1 e2
  pure $ CheckEvaluatesTo e3 cekSuccessTrue

cases_scalarMul_zero :: forall g. TestableAbelianGroup g => Gen Check
cases_scalarMul_zero = do
  p <- arbitraryPlcConst @g
  let e = eqTerm @g (scalarMulTerm @g (integer 0) p) $ zeroTerm @g
  pure $ CheckEvaluatesTo e cekSuccessTrue

cases_scalarMul_one :: forall g. TestableAbelianGroup g => Gen Check
cases_scalarMul_one = do
  p <- arbitraryPlcConst @g
  let e = eqTerm @g (scalarMulTerm @g (integer 1) p) p
  pure $ CheckEvaluatesTo e cekSuccessTrue

cases_scalarMul_inverse :: forall g. TestableAbelianGroup g => Gen Check
cases_scalarMul_inverse = do
  p <- arbitraryPlcConst @g
  let e = eqTerm @g (scalarMulTerm @g (integer (-1)) p) (negTerm @g p)
  pure $ CheckEvaluatesTo e cekSuccessTrue

cases_scalarMul_repeated_addition :: forall g. TestableAbelianGroup g => Gen Check
cases_scalarMul_repeated_addition = do
  n <- resize 100 arbitrary -- number of additions
  p <- arbitraryPlcConst @g
  let e1 = repeatedAdd n p
      e2 = eqTerm @g (scalarMulTerm @g (integer n) p) e1
  pure $ CheckEvaluatesTo e2 cekSuccessTrue
  where
    repeatedAdd :: Integer -> PlcTerm -> PlcTerm
    repeatedAdd n t =
      if n >= 0
        then List.foldl' (addTerm @g) (zeroTerm @g) $ genericReplicate n t
        else repeatedAdd (-n) (negTerm @g t)

cases_scalarMul_periodic :: forall g. TestableAbelianGroup g => Gen Check
cases_scalarMul_periodic = do
  m <- arbitraryPlcScalar
  n <- arbitraryPlcScalar
  p <- arbitraryPlcConst @g
  let e1 = scalarMulTerm @g m p
      k = mkApp2 AddInteger m (mkApp2 MultiplyInteger n (integer scalarPeriod))
      e2 = scalarMulTerm @g k p -- k = m+n|G|
      e = eqTerm @g e1 e2
  pure $ CheckEvaluatesTo e cekSuccessTrue

---------------- Multi-scalar multiplication properties ----------------

cases_multiScalarMul_correct :: forall g. TestableAbelianGroup g => Gen Check
cases_multiScalarMul_correct = do
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
  pure $ CheckEq e1 e2

cases_multiScalarMul_no_scalars :: forall g. TestableAbelianGroup g => Gen Check
cases_multiScalarMul_no_scalars = do
  points <- listOf (arbitrary @g)
  let e = multiScalarMulTerm @g (asPlc ([] @Integer)) (asPlc points)
  pure $ CheckEq e (zeroTerm @g)

cases_multiScalarMul_no_points :: forall g. TestableAbelianGroup g => Gen Check
cases_multiScalarMul_no_points = do
  scalars <- listOf arbitraryMsmScalar
  let e = multiScalarMulTerm @g (asPlc scalars) (asPlc ([] @g))
  pure $ CheckEq e (zeroTerm @g)

cases_multiScalarMul_permutation :: forall g. TestableAbelianGroup g => Gen Check
cases_multiScalarMul_permutation = do
  l <- listOf ((,) <$> arbitraryMsmScalar <*> arbitrary @g)
  l' <- shuffle l
  let (scalars, points) = unzip l
      (scalars', points') = unzip l'
      e1 = multiScalarMulTerm @g (asPlc scalars) (asPlc points)
      e2 = multiScalarMulTerm @g (asPlc scalars') (asPlc points')
  pure $ CheckEq e1 e2

---------------- Uncompression and hashing properties ----------------

cases_roundtrip_compression :: forall g. HashAndCompress g => Gen Check
cases_roundtrip_compression = do
  p <- arbitraryPlcConst @g
  let e = eqTerm @g (uncompressTerm @g (compressTerm @g p)) p
  pure $ CheckEvaluatesTo e cekSuccessTrue

cases_uncompression_wrong_size :: forall g. HashAndCompress g => Gen Check
cases_uncompression_wrong_size = do
  b <- suchThat (resize 128 arbitrary) incorrectSize
  let e = uncompressTerm @g (bytestring b)
  pure $ CheckEvaluatesTo e CekError
  where
    incorrectSize s = BS.length s /= compressedSize @g

cases_uncompress_out_of_group :: forall g. HashAndCompress g => Gen Check
cases_uncompress_out_of_group = do
  b <- suchThat (resize 128 arbitrary) correctSize
  let b' = setBits compressionBit $ clearBits infinityBit b
  let e = uncompressTerm @g (bytestring b')
  pure $ CheckEvaluatesTo e CekError
  where
    correctSize s = BS.length s == compressedSize @g

cases_compression_bit_set :: forall g. HashAndCompress g => Gen Check
cases_compression_bit_set = do
  p <- arbitraryPlcConst @g
  pure $ CheckSatisfies "compression bit set" (compressTerm @g p) hasCompressionBit

cases_clear_compression_bit :: forall g. HashAndCompress g => Gen Check
cases_clear_compression_bit = do
  p <- arbitrary @g
  let b = clearBits compressionBit $ compress @g p
      e = uncompressTerm @g (bytestring b)
  pure $ CheckEvaluatesTo e CekError

cases_flip_sign_bit :: forall g. HashAndCompress g => Gen Check
cases_flip_sign_bit = do
  p <- arbitraryNonZero @g
  let b1 = compress @g p
      b2 = flipBits signBit b1
      e1 = uncompressTerm @g (bytestring b1)
      e2 = uncompressTerm @g (bytestring b2)
      e = eqTerm @g e2 (negTerm @g e1)
  pure $ CheckEvaluatesTo e cekSuccessTrue

cases_set_infinity_bit :: forall g. HashAndCompress g => Gen Check
cases_set_infinity_bit = do
  p <- arbitraryNonZero @g -- This will have the infinity bit set.
  let b = setBits infinityBit $ compress @g p
      e = uncompressTerm @g (bytestring b)
  pure $ CheckEvaluatesTo e CekError

-- We test for hash collisions by generating a list of `numHashCollisionTests`
-- bytestrings, discarding duplicates, hashing the remaining bytestrings, and
-- then checking that no two of the resulting group elements are equal. The time
-- taken by the tests increases quadratically with the number of bytestrings,
-- and is quite long even for numHashCollisionTests = 50.
numHashCollisionInputs :: Int
numHashCollisionInputs = 200

cases_no_hash_collisions :: forall g. HashAndCompress g => Gen Check
cases_no_hash_collisions = do
  let emptyBS = bytestring BS.empty
  msgs <- nub <$> replicateM numHashCollisionInputs arbitrary
  let terms = fmap (\msg -> hashToGroupTerm @g (bytestring msg) emptyBS) msgs
  pure $ CheckDistinct terms

cases_no_hash_collisions_dst :: forall g. HashAndCompress g => Gen Check
cases_no_hash_collisions_dst = do
  let msg = bytestring $ pack [0x01, 0x02]
      maxDstSize = 255
  dsts <- nub <$> replicateM numHashCollisionInputs (resize maxDstSize arbitrary)
  let terms = fmap (\dst -> hashToGroupTerm @g msg (bytestring dst)) dsts
  pure $ CheckDistinct terms

---------------- Pairing properties ----------------

-- Constructing pairing terms

millerLoopTerm :: PlcTerm -> PlcTerm -> PlcTerm
millerLoopTerm = mkApp2 Bls12_381_millerLoop

mulMlResultTerm :: PlcTerm -> PlcTerm -> PlcTerm
mulMlResultTerm = mkApp2 Bls12_381_mulMlResult

finalVerifyTerm :: PlcTerm -> PlcTerm -> PlcTerm
finalVerifyTerm = mkApp2 Bls12_381_finalVerify

cases_pairing_left_additive :: Gen Check
cases_pairing_left_additive = do
  p1 <- arbitraryPlcConst @G1.Element
  p2 <- arbitraryPlcConst @G1.Element
  q <- arbitraryPlcConst @G2.Element
  let e1 = millerLoopTerm (addTerm @G1.Element p1 p2) q
      e2 = mulMlResultTerm (millerLoopTerm p1 q) (millerLoopTerm p2 q)
      e3 = finalVerifyTerm e1 e2
  pure $ CheckEvaluatesTo e3 cekSuccessTrue

cases_pairing_right_additive :: Gen Check
cases_pairing_right_additive = do
  p <- arbitraryPlcConst @G1.Element
  q1 <- arbitraryPlcConst @G2.Element
  q2 <- arbitraryPlcConst @G2.Element
  let e1 = millerLoopTerm p (addTerm @G2.Element q1 q2)
      e2 = mulMlResultTerm (millerLoopTerm p q1) (millerLoopTerm p q2)
      e3 = finalVerifyTerm e1 e2
  pure $ CheckEvaluatesTo e3 cekSuccessTrue

cases_pairing_balanced :: Gen Check
cases_pairing_balanced = do
  n <- arbitraryPlcScalar
  p <- arbitraryPlcConst @G1.Element
  q <- arbitraryPlcConst @G2.Element
  let e1 = millerLoopTerm (scalarMulTerm @G1.Element n p) q
      e2 = millerLoopTerm p (scalarMulTerm @G2.Element n q)
      e3 = finalVerifyTerm e1 e2
  pure $ CheckEvaluatesTo e3 cekSuccessTrue

cases_random_pairing :: Gen Check
cases_random_pairing = do
  p1 <- arbitraryNonZeroPlcConst @G1.Element
  p2 <- arbitraryNonZeroPlcConst @G1.Element
  q1 <- arbitraryNonZeroPlcConst @G2.Element
  q2 <- arbitraryNonZeroPlcConst @G2.Element
  let e = finalVerifyTerm (millerLoopTerm p1 q1) (millerLoopTerm p2 q2)
  pure $ CheckImplies (p1 /= p2 && q1 /= q2) (CheckEvaluatesTo e cekSuccessFalse)

{-| Generate cases for both groups and the pairing properties. Group-valued
outputs are compressed so inputs and results support both textual and Flat formats. -}
generate_bls12_381_properties
  :: OutputFormat -> CheckMode -> PropertyFilter -> FilePath -> Int -> QCGen -> IO [PropertyReport]
generate_bls12_381_properties format mode include outputDir numCases seed = do
  g1 <- generateGroup @G1.Element
  g2 <- generateGroup @G2.Element
  checkUniqueIds (conformanceSuiteDirectory <> ["pairing"]) pairingProperties
  pairing <- catMaybes <$> mapM (emit "pairing" id) pairingProperties
  pure (g1 <> g2 <> pairing)
  where
    emit group encodeResult spec =
      let propertyId =
            PropertyId (conformanceSuiteDirectory <> [group]) (propertySpecId spec)
       in if include propertyId
            then
              Just . PropertyReport propertyId
                <$> generateBlsPropertyFiles
                  format
                  mode
                  outputDir
                  numCases
                  seed
                  propertyId
                  (propertySpecDescription spec)
                  encodeResult
                  (propertySpecCheck spec)
            else pure Nothing
    generateGroup :: forall g. HashAndCompress g => IO [PropertyReport]
    generateGroup = do
      let specs = concatMap snd (groupProperties @g)
      checkUniqueIds (conformanceSuiteDirectory <> [groupName @g]) specs
      catMaybes <$> mapM (emit (groupName @g) (compressTerm @g)) specs

-- | Qualified property names, without sampling inputs or evaluating checks.
bls12_381_property_names :: [PropertyId]
bls12_381_property_names =
  qualified (groupName @G1.Element) (concatMap snd $ groupProperties @G1.Element)
    <> qualified (groupName @G2.Element) (concatMap snd $ groupProperties @G2.Element)
    <> qualified "pairing" pairingProperties
  where
    qualified group =
      map (\spec -> PropertyId (conformanceSuiteDirectory <> [group]) (propertySpecId spec))

conformanceSuiteDirectory :: [String]
conformanceSuiteDirectory = ["bls12_381", "BLS12_381"]
