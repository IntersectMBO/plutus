{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

{-| Tests for [CIP-0123](https://cips.cardano.org/cip/CIP-0123)(the second
batch of bitwise builtins). -}
module Evaluation.Builtins.Bitwise.CIP0123
  ( shiftHomomorphism
  , rotateHomomorphism
  , csbHomomorphism
  , shiftClear
  , rotateRollover
  , csbRotate
  , shiftPosClearLow
  , shiftNegClearHigh
  , posShiftMoveBits
  , negShiftMoveBits
  , rotateMoveBits
  , rotateInverse
  , rotateIdentity
  , csbComplement
  , csbInclusionExclusion
  , csbXor
  , ffsReplicate
  , ffsXor
  , ffsIndex
  , ffsZero
  , shiftMinBound
  , rotateMinBound
  , ffs6453
  , generate_bitwise_cip0123_properties
  ) where

import Evaluation.Builtins.Bitwise.Conformance
import Evaluation.Builtins.Common (PlcTerm)
import Evaluation.Helpers (assertEvaluatesToConstant)

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusCore.Test (mapTestLimitAtLeast)

import Data.Bits qualified as Bits
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Evaluation.Builtins.Conformance (OutputFormat)
import Hedgehog (Gen, Property)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import System.FilePath ((</>))
import Test.QuickCheck.Random (QCGen)
import Test.Tasty (TestTree)
import Test.Tasty.HUnit (testCase)
import Test.Tasty.Hedgehog (testPropertyNamed)

-- | Test for a regression found [here](https://github.com/IntersectMBO/plutus/pull/6453).
ffs6453 :: Property
ffs6453 = checkProperty ffs6453Cases

-- | If given 'Int' 'minBound' as an argument, rotations behave sensibly.
rotateMinBound :: Property
rotateMinBound = checkProperty rotateMinBoundCases

-- | If given 'Int' 'minBound' as an argument, shifts behave sensibly.
shiftMinBound :: Property
shiftMinBound = checkProperty shiftMinBoundCases

-- | Finding the first set bit in a bytestring with only zero bytes should always give -1.
ffsZero :: Property
ffsZero = checkProperty ffsZeroCases

{-| If we find a valid index for the first set bit, then:

1. The specified index should have a set bit; and
2. Any valid smaller index should have a clear bit.

We 'hack' the generator slightly here to ensure we don't end up with all-zeroes (or the empty
bytestring), as otherwise, the test wouldn't be meaningful. -}
ffsIndex :: Property
ffsIndex = checkProperty ffsIndexCases

{-| For any choice of bytestring, if we XOR it with itself, there should be no set bits; that is,
finding the first set bit should give @-1@. -}
ffsXor :: Property
ffsXor = checkProperty ffsXorCases

{-| If we replicate any byte any (positive) number of times, the first set bit
should be the same as in the case where we replicated it exactly once. -}
ffsReplicate :: Property
ffsReplicate = checkProperty ffsReplicateCases

{-| For any bytestring whose bit length is @n@ and has @k@ set bits, its complement should have
@n - k@ set bits. -}
csbComplement :: Property
csbComplement = checkProperty csbComplementCases

{-| The inclusion-exclusion principle: specifically, for any @x@ and @y@, the number of set bits in
@x XOR y@ should be the number of set bits in @x OR y@ minus the number of set bits in @x AND y@. -}
csbInclusionExclusion :: Property
csbInclusionExclusion = checkProperty csbInclusionExclusionCases

-- | For any bytestring @x@, the number of set bits in @x XOR x@ should be 0.
csbXor :: Property
csbXor = checkProperty csbXorCases

{-| There should exist a monoid homomorphism between natural number addition
and function composition for shifts over a fixed bytestring argument. -}
shiftHomomorphism :: [TestTree]
shiftHomomorphism =
  [ testPropertyNamed "zero shift is identity" "zero_shift_id" $
      mapTestLimitAtLeast 99 (`div` 10) idProp
  , -- Because the homomorphism on shifts is more restrictive than on rotations (namely, it is for
    -- naturals and their negative equivalents, not integers), we separate the composition property
    -- into two: one dealing with non-negative, the other with non-positive. This helps a bit with
    -- coverage, as otherwise, we wouldn't necessarily cover both paths equally well, as we'd have to
    -- either discard mismatched signs (which are likely) or 'hack them in-place', which would skew
    -- distributions.
    testPropertyNamed "non-negative addition of shifts is composition" "plus_shift_pos_comp" $
      mapTestLimitAtLeast 50 (`div` 20) plusCompProp
  , testPropertyNamed "non-positive addition of shifts is composition" "plus_shift_neg_comp" $
      mapTestLimitAtLeast 50 (`div` 20) minusCompProp
  ]
  where
    idProp :: Property
    idProp = checkProperty shiftIdentityCases
    plusCompProp :: Property
    plusCompProp = checkProperty shiftPlusCompCases
    minusCompProp :: Property
    minusCompProp = checkProperty shiftMinusCompCases

{-| There should exist a monoid homomorphism between integer addition and function composition for
rotations over a fixed bytestring argument. -}
rotateHomomorphism :: [TestTree]
rotateHomomorphism =
  [ testPropertyNamed "zero rotation is identity" "zero_rotate_id" $
      mapTestLimitAtLeast 99 (`div` 10) idProp
  , testPropertyNamed "addition of rotations is composition" "plus_rotate_comp" $
      mapTestLimitAtLeast 50 (`div` 20) compProp
  ]
  where
    idProp :: Property
    idProp = checkProperty rotateIdentityHomomorphismCases
    compProp :: Property
    compProp = checkProperty rotateCompCases

-- | A pos rotation and neg rotation cancel each other out.
rotateInverse :: Property
rotateInverse = checkProperty rotateInverseCases

-- | Rotation with multiples of @bitLen@ is identity.
rotateIdentity :: Property
rotateIdentity = checkProperty rotateIdentityCases

{-| There should exist a monoid homomorphism between bytestring concatenation and natural number
addition. -}
csbHomomorphism :: [TestTree]
csbHomomorphism =
  [ testCase "count of empty is zero" $ assertEvaluatesToConstant @Integer 0 csbEmptyTerm
  , testPropertyNamed "count of concat is addition" "concat_count_plus" $
      mapTestLimitAtLeast 50 (`div` 20) compProp
  ]
  where
    compProp :: Property
    compProp = checkProperty csbCompCases

-- | Shifting by more than the bit length (either positive or negative) clears the result.
shiftClear :: Property
shiftClear = checkProperty shiftClearCases

-- | Positive shifts clear low-index bits.
shiftPosClearLow :: Property
shiftPosClearLow = checkProperty shiftPosClearLowCases

-- | Negative shifts clear high-index bits.
shiftNegClearHigh :: Property
shiftNegClearHigh = checkProperty shiftNegClearHighCases

posShiftMoveBits :: Property
posShiftMoveBits = checkProperty posShiftMoveBitsCases

negShiftMoveBits :: Property
negShiftMoveBits = checkProperty negShiftMoveBitsCases

-- | Rotations by more than the bit length 'roll over' bits.
rotateRollover :: Property
rotateRollover = checkProperty rotateRolloverCases

-- | Rotations move bits, but don't change them.
rotateMoveBits :: Property
rotateMoveBits = checkProperty rotateMoveBitsCases

-- | Rotations do not change how many set (and clear) bits there are.
csbRotate :: Property
csbRotate = checkProperty csbRotateCases

-- Shared case generators: normal tests assert the checks; export only consumes their terms.

ffs6453Cases :: Gen Check
ffs6453Cases = do
  -- Generate a suffix that is an exact multiple of 8 bytes, all zero
  suffixLenMult <- Gen.integral . Range.linear 1 $ 10
  let suffix = BS.replicate (8 * suffixLenMult) 0x00
  -- Generate a prefix nonzero byte
  prefix <- Gen.word8 . Range.constant 0x01 $ 0xFF
  let expected = 8 * BS.length suffix + Bits.countTrailingZeros prefix
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.FindFirstSetBit)
          [ mkConstant @ByteString () . BS.cons prefix $ suffix
          ]
  checkConstant @Integer (fromIntegral expected) lhs

rotateMinBoundCases :: Gen Check
rotateMinBoundCases = do
  bs <- genByteString 1 512
  let bitLen = fromIntegral $ BS.length bs * 8
  -- By the laws of rotations, we know that we can perform a modular reduction on
  -- the argument and not change the result we get. Thus, we (via Integer) do
  -- this exact reduction on minBound, then compare the result of running a
  -- rotation using this reduced argument versus the actual argument.
  let minBoundInt = fromIntegral (minBound :: Int)
  let minBoundIntReduced = negate (abs minBoundInt `rem` bitLen)
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () minBoundInt
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () minBoundIntReduced
          ]
  checkSame lhs rhs

shiftMinBoundCases :: Gen Check
shiftMinBoundCases = do
  bs <- genByteString 0 512
  let len = BS.length bs
  let shiftExp =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () . fromIntegral $ (minBound :: Int)
          ]
  checkConstant @ByteString (BS.replicate len 0x00) shiftExp

ffsZeroCases :: Gen Check
ffsZeroCases = do
  len <- Gen.integral . Range.linear 0 $ 512
  let bs = BS.replicate len 0x00
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.FindFirstSetBit)
          [ mkConstant @ByteString () bs
          ]
  checkConstant @Integer (negate 1) rhs

ffsIndexCases :: Gen Check
ffsIndexCases = do
  bs <- genByteStringThat (BS.any (/= 0x00)) 0 512
  let ffsExp =
        mkIterAppNoAnn
          (builtin () PLC.FindFirstSetBit)
          [ mkConstant @ByteString () bs
          ]
  -- Choose subsequent indices using a reference calculation, keeping generation
  -- independent of builtin evaluation. The generator guarantees a nonzero byte.
  let ix =
        toInteger $
          head
            [ 8 * byteIndex + Bits.countTrailingZeros byte
            | (byteIndex, byte) <- zip [0 ..] (BS.unpack (BS.reverse bs))
            , byte /= 0
            ]
  let hitIxExp =
        mkIterAppNoAnn
          (builtin () PLC.ReadBit)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () ix
          ]
  found <- checkConstant ix ffsExp
  hit <- checkConstant True hitIxExp
  if ix == 0
    then pure $ CheckBoth found hit
    else do
      i <- Gen.integral . Range.linear 0 $ ix - 1
      let missIxExp =
            mkIterAppNoAnn
              (builtin () PLC.ReadBit)
              [ mkConstant @ByteString () bs
              , mkConstant @Integer () i
              ]
      miss <- checkConstant False missIxExp
      pure $ CheckBoth found (CheckBoth hit miss)

ffsXorCases :: Gen Check
ffsXorCases = do
  bs <- genByteString 0 512
  semantics <- Gen.bool
  let rhsInner =
        mkIterAppNoAnn
          (builtin () PLC.XorByteString)
          [ mkConstant @Bool () semantics
          , mkConstant @ByteString () bs
          , mkConstant @ByteString () bs
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.FindFirstSetBit)
          [ rhsInner
          ]
  checkConstant @Integer (negate 1) rhs

ffsReplicateCases :: Gen Check
ffsReplicateCases = do
  n <- Gen.integral . Range.linear 1 $ 512
  w8 <- Gen.integral . Range.linear 0 $ 255
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.ReplicateByte)
          [ mkConstant @Integer () n
          , mkConstant @Integer () w8
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.FindFirstSetBit)
          [ lhsInner
          ]
  let rhsInner =
        mkIterAppNoAnn
          (builtin () PLC.ReplicateByte)
          [ mkConstant @Integer () 1
          , mkConstant @Integer () w8
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.FindFirstSetBit)
          [ rhsInner
          ]
  checkSame lhs rhs

csbComplementCases :: Gen Check
csbComplementCases = do
  bs <- genByteString 0 512
  let bitLen = BS.length bs * 8
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ mkConstant @ByteString () bs
          ]
  let rhsComplement =
        mkIterAppNoAnn
          (builtin () PLC.ComplementByteString)
          [ mkConstant @ByteString () bs
          ]
  let rhsCount =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ rhsComplement
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.SubtractInteger)
          [ mkConstant @Integer () (fromIntegral bitLen)
          , rhsCount
          ]
  checkSame lhs rhs

csbInclusionExclusionCases :: Gen Check
csbInclusionExclusionCases = do
  x <- genByteString 0 512
  y <- genByteString 0 512
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.XorByteString)
          [ mkConstant @Bool () False
          , mkConstant @ByteString () x
          , mkConstant @ByteString () y
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ lhsInner
          ]
  let rhsOr =
        mkIterAppNoAnn
          (builtin () PLC.OrByteString)
          [ mkConstant @Bool () False
          , mkConstant @ByteString () x
          , mkConstant @ByteString () y
          ]
  let rhsAnd =
        mkIterAppNoAnn
          (builtin () PLC.AndByteString)
          [ mkConstant @Bool () False
          , mkConstant @ByteString () x
          , mkConstant @ByteString () y
          ]
  let rhsCountOr =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ rhsOr
          ]
  let rhsCountAnd =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ rhsAnd
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.SubtractInteger)
          [ rhsCountOr
          , rhsCountAnd
          ]
  checkSame lhs rhs

csbXorCases :: Gen Check
csbXorCases = do
  bs <- genByteString 0 512
  semantics <- Gen.bool
  let rhsInner =
        mkIterAppNoAnn
          (builtin () PLC.XorByteString)
          [ mkConstant @Bool () semantics
          , mkConstant @ByteString () bs
          , mkConstant @ByteString () bs
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ rhsInner
          ]
  checkConstant @Integer 0 rhs

shiftIdentityCases :: Gen Check
shiftIdentityCases = do
  bs <- genByteString 0 512
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () 0
          ]
  checkConstant bs lhs

shiftPlusCompCases :: Gen Check
shiftPlusCompCases = do
  bs <- genByteString 0 512
  i <- Gen.integral . Range.linear 0 $ 512
  j <- Gen.integral . Range.linear 0 $ 512
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.AddInteger)
          [ mkConstant @Integer () i
          , mkConstant @Integer () j
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , lhsInner
          ]
  let rhsInner =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () i
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ rhsInner
          , mkConstant @Integer () j
          ]
  checkSame lhs rhs

shiftMinusCompCases :: Gen Check
shiftMinusCompCases = do
  bs <- genByteString 0 512
  i <- Gen.integral . Range.linear 0 $ negate 512
  j <- Gen.integral . Range.linear 0 $ negate 512
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.AddInteger)
          [ mkConstant @Integer () i
          , mkConstant @Integer () j
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , lhsInner
          ]
  let rhsInner =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () i
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ rhsInner
          , mkConstant @Integer () j
          ]
  checkSame lhs rhs

rotateIdentityHomomorphismCases :: Gen Check
rotateIdentityHomomorphismCases = do
  bs <- genByteString 0 512
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () 0
          ]
  checkConstant bs lhs

rotateCompCases :: Gen Check
rotateCompCases = do
  bs <- genByteString 0 512
  i <- Gen.integral . Range.linear (negate 512) $ 512
  j <- Gen.integral . Range.linear (negate 512) $ 512
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.AddInteger)
          [ mkConstant @Integer () i
          , mkConstant @Integer () j
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , lhsInner
          ]
  let rhsInner =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () i
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ rhsInner
          , mkConstant @Integer () j
          ]
  checkSame lhs rhs

rotateInverseCases :: Gen Check
rotateInverseCases = do
  bs <- genByteString 0 512
  i <- Gen.integral $ Range.linear (-512) 512
  let rotated =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () i
          ]
  let inverted =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ rotated
          , mkConstant @Integer () (negate i)
          ]
  checkConstant bs inverted

rotateIdentityCases :: Gen Check
rotateIdentityCases = do
  bs <- genByteString 0 512
  k <- Gen.integral $ Range.linear 1 16
  let bitLen = toInteger (BS.length bs * 8)
  let rotated =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () (k * bitLen)
          ]
  checkConstant bs rotated

csbCompCases :: Gen Check
csbCompCases = do
  bs1 <- genByteString 0 512
  bs2 <- genByteString 0 512
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.AppendByteString)
          [ mkConstant @ByteString () bs1
          , mkConstant @ByteString () bs2
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ lhsInner
          ]
  let rhsLeft =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ mkConstant @ByteString () bs1
          ]
  let rhsRight =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ mkConstant @ByteString () bs2
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.AddInteger)
          [ rhsLeft
          , rhsRight
          ]
  checkSame lhs rhs

shiftClearCases :: Gen Check
shiftClearCases = do
  bs <- genByteString 0 512
  let bitLen = 8 * BS.length bs
  i <- Gen.integral . Range.linear (negate 256) $ 256
  adjustment <- case signum i of
    (-1) -> pure $ negate bitLen + i
    -- Here, we shift by the length exactly, so we randomly pick negative or positive
    0 -> Gen.element $ [bitLen, negate bitLen]
    _ -> pure $ bitLen + i
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () (fromIntegral adjustment)
          ]
  let rhsInner =
        mkIterAppNoAnn
          (builtin () PLC.LengthOfByteString)
          [ mkConstant @ByteString () bs
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.ReplicateByte)
          [ rhsInner
          , mkConstant @Integer () 0
          ]
  checkSame lhs rhs

shiftPosClearLowCases :: Gen Check
shiftPosClearLowCases = do
  bs <- genByteString 1 512
  let bitLen = 8 * BS.length bs
  n <- Gen.integral . Range.linear 1 $ bitLen - 1
  i <- Gen.integral . Range.linear 0 $ n - 1
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () (fromIntegral n)
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ReadBit)
          [ lhsInner
          , mkConstant @Integer () (fromIntegral i)
          ]
  checkConstant False lhs

shiftNegClearHighCases :: Gen Check
shiftNegClearHighCases = do
  bs <- genByteString 1 512
  let bitLen = 8 * BS.length bs
  n <- Gen.integral . Range.linear 1 $ bitLen - 1
  i <- Gen.integral . Range.linear 0 $ n - 1
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () (fromIntegral . negate $ n)
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ReadBit)
          [ lhsInner
          , mkConstant @Integer () (fromIntegral $ bitLen - i - 1)
          ]
  checkConstant False lhs

posShiftMoveBitsCases :: Gen Check
posShiftMoveBitsCases = do
  n <- Gen.integral $ Range.linear 1 7
  b <- Gen.enumBounded
  let bs = BS.singleton b
  let shifted =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () n
          ]
  checkConstant (BS.singleton $ b `Bits.shiftL` fromInteger n) shifted

negShiftMoveBitsCases :: Gen Check
negShiftMoveBitsCases = do
  n <- Gen.integral $ Range.linear 1 7
  b <- Gen.enumBounded
  let bs = BS.singleton b
  let shifted =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () (negate n)
          ]
  checkConstant (BS.singleton $ b `Bits.shiftR` fromInteger n) shifted

rotateRolloverCases :: Gen Check
rotateRolloverCases = do
  bs <- genByteString 0 512
  let bitLen = 8 * BS.length bs
  i <- Gen.integral . Range.linear (negate 512) $ 512
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer
              ()
              ( case signum i of
                  (-1) -> (negate . fromIntegral $ bitLen) + i
                  _ -> fromIntegral bitLen + i
              )
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () i
          ]
  checkSame lhs rhs

rotateMoveBitsCases :: Gen Check
rotateMoveBitsCases = do
  bs <- genByteString 1 512
  let bitLen = 8 * BS.length bs
  i <- Gen.integral . Range.linear 0 $ bitLen - 1
  j <- Gen.integral . Range.linear (negate 256) $ 256
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ReadBit)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () (fromIntegral i)
          ]
  let rhsRotation =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () (fromIntegral j)
          ]
  let rhsIndex =
        mkIterAppNoAnn
          (builtin () PLC.ModInteger)
          [ mkConstant @Integer () (fromIntegral $ i + j)
          , mkConstant @Integer () (fromIntegral bitLen)
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.ReadBit)
          [ rhsRotation
          , rhsIndex
          ]
  checkSame lhs rhs

csbRotateCases :: Gen Check
csbRotateCases = do
  bs <- genByteString 0 512
  i <- Gen.integral . Range.linear (negate 512) $ 512
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ mkConstant @ByteString () bs
          ]
  let rhsInner =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () i
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.CountSetBits)
          [ rhsInner
          ]
  checkSame lhs rhs

csbEmptyTerm :: PlcTerm
csbEmptyTerm = mkIterAppNoAnn (builtin () PLC.CountSetBits) [mkConstant @ByteString () ""]

-- | Emit cases for all the properties, including the fixed empty-input check.
generate_bitwise_cip0123_properties :: OutputFormat -> FilePath -> Int -> QCGen -> IO ()
generate_bitwise_cip0123_properties format outputDir numFiles seed =
  mapM_
    (\(name, gen) -> generateBitwisePropertyFiles format suiteDir numFiles seed name gen)
    conformanceProperties
  where
    suiteDir = outputDir </> "bitwise" </> "CIP0123"

conformanceProperties :: [(String, Gen Check)]
conformanceProperties =
  [ ("shiftHomomorphism_idProp", shiftIdentityCases)
  , ("shiftHomomorphism_plusCompProp", shiftPlusCompCases)
  , ("shiftHomomorphism_minusCompProp", shiftMinusCompCases)
  , ("rotateHomomorphism_idProp", rotateIdentityHomomorphismCases)
  , ("rotateHomomorphism_compProp", rotateCompCases)
  , ("csbHomomorphism_empty", checkConstant @Integer 0 csbEmptyTerm)
  , ("csbHomomorphism_compProp", csbCompCases)
  , ("shiftClear", shiftClearCases)
  , ("rotateRollover", rotateRolloverCases)
  , ("csbRotate", csbRotateCases)
  , ("shiftPosClearLow", shiftPosClearLowCases)
  , ("shiftNegClearHigh", shiftNegClearHighCases)
  , ("posShiftMoveBits", posShiftMoveBitsCases)
  , ("negShiftMoveBits", negShiftMoveBitsCases)
  , ("rotateMoveBits", rotateMoveBitsCases)
  , ("rotateInverse", rotateInverseCases)
  , ("rotateIdentity", rotateIdentityCases)
  , ("csbComplement", csbComplementCases)
  , ("csbInclusionExclusion", csbInclusionExclusionCases)
  , ("csbXor", csbXorCases)
  , ("ffsReplicate", ffsReplicateCases)
  , ("ffsXor", ffsXorCases)
  , ("ffsIndex", ffsIndexCases)
  , ("ffsZero", ffsZeroCases)
  , ("shiftMinBound", shiftMinBoundCases)
  , ("rotateMinBound", rotateMinBoundCases)
  , ("ffs6453", ffs6453Cases)
  ]
