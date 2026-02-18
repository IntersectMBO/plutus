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
  ) where

import Evaluation.Helpers
  ( assertEvaluatesToConstant
  , evaluateTheSame
  , evaluateToHaskell
  , evaluatesToConstant
  , forAllByteString
  , forAllByteStringThat
  )

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusCore.Test (mapTestLimitAtLeast)

import Control.Monad (unless)
import Data.Bits qualified as Bits
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Hedgehog (Property, forAll, property)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree)
import Test.Tasty.HUnit (testCase)
import Test.Tasty.Hedgehog (testPropertyNamed)

-- | Test for a regression found [here](https://github.com/IntersectMBO/plutus/pull/6453).
ffs6453 :: Property
ffs6453 = property $ do
  -- Generate a suffix that is an exact multiple of 8 bytes, all zero
  suffixLenMult <- forAll . Gen.integral . Range.linear 1 $ 10
  let suffix = BS.replicate (8 * suffixLenMult) 0x00
  -- Generate a prefix nonzero byte
  prefix <- forAll . Gen.word8 . Range.constant 0x01 $ 0xFF
  let expected = 8 * BS.length suffix + Bits.countTrailingZeros prefix
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.FindFirstSetBit)
          [ mkConstant @ByteString () . BS.cons prefix $ suffix
          ]
  evaluatesToConstant @Integer (fromIntegral expected) lhs

-- | If given 'Int' 'minBound' as an argument, rotations behave sensibly.
rotateMinBound :: Property
rotateMinBound = property $ do
  bs <- forAllByteString 1 512
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
  evaluateTheSame lhs rhs

-- | If given 'Int' 'minBound' as an argument, shifts behave sensibly.
shiftMinBound :: Property
shiftMinBound = property $ do
  bs <- forAllByteString 0 512
  let len = BS.length bs
  let shiftExp =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () . fromIntegral $ (minBound :: Int)
          ]
  evaluatesToConstant @ByteString (BS.replicate len 0x00) shiftExp

-- | Finding the first set bit in a bytestring with only zero bytes should always give -1.
ffsZero :: Property
ffsZero = property $ do
  len <- forAll . Gen.integral . Range.linear 0 $ 512
  let bs = BS.replicate len 0x00
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.FindFirstSetBit)
          [ mkConstant @ByteString () bs
          ]
  evaluatesToConstant @Integer (negate 1) rhs

{-| If we find a valid index for the first set bit, then:

1. The specified index should have a set bit; and
2. Any valid smaller index should have a clear bit.

We 'hack' the generator slightly here to ensure we don't end up with all-zeroes (or the empty
bytestring), as otherwise, the test wouldn't be meaningful. -}
ffsIndex :: Property
ffsIndex = property $ do
  bs <- forAllByteStringThat (BS.any (/= 0x00)) 0 512
  let ffsExp =
        mkIterAppNoAnn
          (builtin () PLC.FindFirstSetBit)
          [ mkConstant @ByteString () bs
          ]
  ix <- evaluateToHaskell ffsExp
  let hitIxExp =
        mkIterAppNoAnn
          (builtin () PLC.ReadBit)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () ix
          ]
  evaluatesToConstant True hitIxExp
  unless (ix == 0) $ do
    i <- forAll . Gen.integral . Range.linear 0 $ ix - 1
    let missIxExp =
          mkIterAppNoAnn
            (builtin () PLC.ReadBit)
            [ mkConstant @ByteString () bs
            , mkConstant @Integer () i
            ]
    evaluatesToConstant False missIxExp

{-| For any choice of bytestring, if we XOR it with itself, there should be no set bits; that is,
finding the first set bit should give @-1@. -}
ffsXor :: Property
ffsXor = property $ do
  bs <- forAllByteString 0 512
  semantics <- forAll Gen.bool
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
  evaluatesToConstant @Integer (negate 1) rhs

{-| If we replicate any byte any (positive) number of times, the first set bit
should be the same as in the case where we replicated it exactly once. -}
ffsReplicate :: Property
ffsReplicate = property $ do
  n <- forAll . Gen.integral . Range.linear 1 $ 512
  w8 <- forAll . Gen.integral . Range.linear 0 $ 255
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
  evaluateTheSame lhs rhs

{-| For any bytestring whose bit length is @n@ and has @k@ set bits, its complement should have
@n - k@ set bits. -}
csbComplement :: Property
csbComplement = property $ do
  bs <- forAllByteString 0 512
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
  evaluateTheSame lhs rhs

{-| The inclusion-exclusion principle: specifically, for any @x@ and @y@, the number of set bits in
@x XOR y@ should be the number of set bits in @x OR y@ minus the number of set bits in @x AND y@. -}
csbInclusionExclusion :: Property
csbInclusionExclusion = property $ do
  x <- forAllByteString 0 512
  y <- forAllByteString 0 512
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
  evaluateTheSame lhs rhs

-- | For any bytestring @x@, the number of set bits in @x XOR x@ should be 0.
csbXor :: Property
csbXor = property $ do
  bs <- forAllByteString 0 512
  semantics <- forAll Gen.bool
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
  evaluatesToConstant @Integer 0 rhs

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
    idProp = property $ do
      bs <- forAllByteString 0 512
      let lhs =
            mkIterAppNoAnn
              (builtin () PLC.ShiftByteString)
              [ mkConstant @ByteString () bs
              , mkConstant @Integer () 0
              ]
      evaluatesToConstant bs lhs
    plusCompProp :: Property
    plusCompProp = property $ do
      bs <- forAllByteString 0 512
      i <- forAll . Gen.integral . Range.linear 0 $ 512
      j <- forAll . Gen.integral . Range.linear 0 $ 512
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
      evaluateTheSame lhs rhs
    minusCompProp :: Property
    minusCompProp = property $ do
      bs <- forAllByteString 0 512
      i <- forAll . Gen.integral . Range.linear 0 $ negate 512
      j <- forAll . Gen.integral . Range.linear 0 $ negate 512
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
      evaluateTheSame lhs rhs

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
    idProp = property $ do
      bs <- forAllByteString 0 512
      let lhs =
            mkIterAppNoAnn
              (builtin () PLC.RotateByteString)
              [ mkConstant @ByteString () bs
              , mkConstant @Integer () 0
              ]
      evaluatesToConstant bs lhs
    compProp :: Property
    compProp = property $ do
      bs <- forAllByteString 0 512
      i <- forAll . Gen.integral . Range.linear (negate 512) $ 512
      j <- forAll . Gen.integral . Range.linear (negate 512) $ 512
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
      evaluateTheSame lhs rhs

-- | A pos rotation and neg rotation cancel each other out.
rotateInverse :: Property
rotateInverse = property $ do
  bs <- forAllByteString 0 512
  i <- forAll . Gen.integral $ Range.linear (-512) 512
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
  evaluatesToConstant bs inverted

-- | Rotation with multiples of @bitLen@ is identity.
rotateIdentity :: Property
rotateIdentity = property $ do
  bs <- forAllByteString 0 512
  k <- forAll . Gen.integral $ Range.linear 1 16
  let bitLen = toInteger (BS.length bs * 8)
  let rotated =
        mkIterAppNoAnn
          (builtin () PLC.RotateByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () (k * bitLen)
          ]
  evaluatesToConstant bs rotated

{-| There should exist a monoid homomorphism between bytestring concatenation and natural number
addition. -}
csbHomomorphism :: [TestTree]
csbHomomorphism =
  [ testCase "count of empty is zero" $ do
      let lhs =
            mkIterAppNoAnn
              (builtin () PLC.CountSetBits)
              [ mkConstant @ByteString () ""
              ]
      assertEvaluatesToConstant @Integer 0 lhs
  , testPropertyNamed "count of concat is addition" "concat_count_plus" $
      mapTestLimitAtLeast 50 (`div` 20) compProp
  ]
  where
    compProp :: Property
    compProp = property $ do
      bs1 <- forAllByteString 0 512
      bs2 <- forAllByteString 0 512
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
      evaluateTheSame lhs rhs

-- | Shifting by more than the bit length (either positive or negative) clears the result.
shiftClear :: Property
shiftClear = property $ do
  bs <- forAllByteString 0 512
  let bitLen = 8 * BS.length bs
  i <- forAll . Gen.integral . Range.linear (negate 256) $ 256
  adjustment <- case signum i of
    (-1) -> pure $ negate bitLen + i
    -- Here, we shift by the length exactly, so we randomly pick negative or positive
    0 -> forAll . Gen.element $ [bitLen, negate bitLen]
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
  evaluateTheSame lhs rhs

-- | Positive shifts clear low-index bits.
shiftPosClearLow :: Property
shiftPosClearLow = property $ do
  bs <- forAllByteString 1 512
  let bitLen = 8 * BS.length bs
  n <- forAll . Gen.integral . Range.linear 1 $ bitLen - 1
  i <- forAll . Gen.integral . Range.linear 0 $ n - 1
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
  evaluatesToConstant False lhs

-- | Negative shifts clear high-index bits.
shiftNegClearHigh :: Property
shiftNegClearHigh = property $ do
  bs <- forAllByteString 1 512
  let bitLen = 8 * BS.length bs
  n <- forAll . Gen.integral . Range.linear 1 $ bitLen - 1
  i <- forAll . Gen.integral . Range.linear 0 $ n - 1
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
  evaluatesToConstant False lhs

posShiftMoveBits :: Property
posShiftMoveBits = property $ do
  n <- forAll . Gen.integral $ Range.linear 1 7
  let bs = BS.singleton 0x01
  let shifted =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () n
          ]
  evaluatesToConstant (BS.singleton $ 0x01 `Bits.shiftL` fromInteger n) shifted

negShiftMoveBits :: Property
negShiftMoveBits = property $ do
  n <- forAll . Gen.integral $ Range.linear 1 7
  let bs = BS.singleton 0x80
  let shifted =
        mkIterAppNoAnn
          (builtin () PLC.ShiftByteString)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () (negate n)
          ]
  evaluatesToConstant (BS.singleton $ 0x80 `Bits.shiftR` fromInteger n) shifted

-- | Rotations by more than the bit length 'roll over' bits.
rotateRollover :: Property
rotateRollover = property $ do
  bs <- forAllByteString 0 512
  let bitLen = 8 * BS.length bs
  i <- forAll . Gen.integral . Range.linear (negate 512) $ 512
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
  evaluateTheSame lhs rhs

-- | Rotations move bits, but don't change them.
rotateMoveBits :: Property
rotateMoveBits = property $ do
  bs <- forAllByteString 1 512
  let bitLen = 8 * BS.length bs
  i <- forAll . Gen.integral . Range.linear 0 $ bitLen - 1
  j <- forAll . Gen.integral . Range.linear (negate 256) $ 256
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
  evaluateTheSame lhs rhs

-- | Rotations do not change how many set (and clear) bits there are.
csbRotate :: Property
csbRotate = property $ do
  bs <- forAllByteString 0 512
  i <- forAll . Gen.integral . Range.linear (negate 512) $ 512
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
  evaluateTheSame lhs rhs
