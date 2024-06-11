-- editorconfig-checker-disable-file

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

-- | Tests for [this
-- CIP](https://github.com/mlabs-haskell/CIPs/blob/koz/bitwise/CIP-XXXX/CIP-XXXX.md)
module Evaluation.Builtins.Bitwise (
  shiftHomomorphism,
  rotateHomomorphism,
  csbHomomorphism,
  shiftClear,
  rotateRollover,
  csbRotate,
  shiftPosClearLow,
  shiftNegClearHigh,
  rotateMoveBits,
  csbComplement,
  csbInclusionExclusion,
  csbXor,
  ffsReplicate,
  ffsXor,
  ffsIndex,
  ffsZero
  ) where

import Control.Monad (unless)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Evaluation.Builtins.Common (typecheckEvaluateCek, typecheckReadKnownCek)
import Hedgehog (Property, PropertyT, annotateShow, failure, forAll, forAllWith, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Numeric (showHex)
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModelForTesting)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusPrelude (Word8, def)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import UntypedPlutusCore qualified as UPLC

-- | Finding the first set bit in a bytestring with only zero bytes should always give -1.
ffsZero :: Property
ffsZero = property $ do
  len <- forAll . Gen.integral . Range.linear 0 $ 1024
  let bs = BS.replicate len 0x00
  let rhs = mkIterAppNoAnn (builtin () PLC.FindFirstSetBit) [
        mkConstant @ByteString () bs
        ]
  evaluateAndVerify (mkConstant @Integer () (negate 1)) rhs

-- | If we find a valid index for the first set bit, then:
--
-- 1. The specified index should have a set bit; and
-- 2. Any valid smaller index should have a clear bit.
--
-- We 'hack' the generator slightly here to ensure we don't end up with all-zeroes (or the empty
-- bytestring), as otherwise, the test wouldn't be meaningful.
ffsIndex :: Property
ffsIndex = property $ do
  bs <- forAllNonZeroByteString
  let ffsExp = mkIterAppNoAnn (builtin () PLC.FindFirstSetBit) [
        mkConstant @ByteString () bs
        ]
  case typecheckReadKnownCek def defaultBuiltinCostModelForTesting ffsExp of
    Left err -> annotateShow err >> failure
    Right (Left err) -> annotateShow err >> failure
    Right (Right ix) -> do
      let hitIxExp = mkIterAppNoAnn (builtin () PLC.ReadBit) [
            mkConstant @ByteString () bs,
            mkConstant @Integer () ix
            ]
      evaluateAndVerify (mkConstant @Bool () True) hitIxExp
      unless (ix == 0) $ do
        i <- forAll . Gen.integral . Range.linear 0 $ ix - 1
        let missIxExp = mkIterAppNoAnn (builtin () PLC.ReadBit) [
              mkConstant @ByteString () bs,
              mkConstant @Integer () i
              ]
        evaluateAndVerify (mkConstant @Bool () False) missIxExp

-- | For any choice of bytestring, if we XOR it with itself, there should be no set bits; that is,
-- finding the first set bit should give @-1@.
ffsXor :: Property
ffsXor = property $ do
  bs <- forAllByteString
  semantics <- forAll Gen.bool
  let rhsInner = mkIterAppNoAnn (builtin () PLC.XorByteString) [
        mkConstant @Bool () semantics,
        mkConstant @ByteString () bs,
        mkConstant @ByteString () bs
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.FindFirstSetBit) [
        rhsInner
        ]
  evaluateAndVerify (mkConstant @Integer () (negate 1)) rhs

-- | If we replicate any byte any (positive) number of times, the first set bit should be the same as
-- in the case where we replicated it exactly once.
ffsReplicate :: Property
ffsReplicate = property $ do
  n <- forAll . Gen.integral . Range.linear 1 $ 512
  w8 <- forAll . Gen.integral . Range.linear 0 $ 255
  let lhsInner = mkIterAppNoAnn (builtin () PLC.ReplicateByte) [
        mkConstant @Integer () n,
        mkConstant @Integer () w8
        ]
  let lhs = mkIterAppNoAnn (builtin () PLC.FindFirstSetBit) [
        lhsInner
        ]
  let rhsInner = mkIterAppNoAnn (builtin () PLC.ReplicateByte) [
        mkConstant @Integer () 1,
        mkConstant @Integer () w8
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.FindFirstSetBit) [
        rhsInner
        ]
  evaluateTheSame lhs rhs

-- | For any bytestring whose bit length is @n@ and has @k@ set bits, its complement should have
-- @n - k@ set bits.
csbComplement :: Property
csbComplement = property $ do
  bs <- forAllByteString
  let bitLen = BS.length bs * 8
  let lhs = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
        mkConstant @ByteString () bs
        ]
  let rhsComplement = mkIterAppNoAnn (builtin () PLC.ComplementByteString) [
        mkConstant @ByteString () bs
        ]
  let rhsCount = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
        rhsComplement
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.SubtractInteger) [
        mkConstant @Integer () (fromIntegral bitLen),
        rhsCount
        ]
  evaluateTheSame lhs rhs

-- | The inclusion-exclusion principle: specifically, for any @x@ and @y@, the number of set bits in
-- @x XOR y@ should be the number of set bits in @x OR y@ minus the number of set bits in @x AND y@.
csbInclusionExclusion :: Property
csbInclusionExclusion = property $ do
  x <- forAllByteString
  y <- forAllByteString
  let lhsInner = mkIterAppNoAnn (builtin () PLC.XorByteString) [
        mkConstant @Bool () False,
        mkConstant @ByteString () x,
        mkConstant @ByteString () y
        ]
  let lhs = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
        lhsInner
        ]
  let rhsOr = mkIterAppNoAnn (builtin () PLC.OrByteString) [
        mkConstant @Bool () False,
        mkConstant @ByteString () x,
        mkConstant @ByteString () y
        ]
  let rhsAnd = mkIterAppNoAnn (builtin () PLC.AndByteString) [
        mkConstant @Bool () False,
        mkConstant @ByteString () x,
        mkConstant @ByteString () y
        ]
  let rhsCountOr = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
        rhsOr
        ]
  let rhsCountAnd = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
        rhsAnd
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.SubtractInteger) [
        rhsCountOr,
        rhsCountAnd
        ]
  evaluateTheSame lhs rhs

-- | For any bytestring @x@, the number of set bits in @x XOR x@ should be 0.
csbXor :: Property
csbXor = property $ do
  bs <- forAllByteString
  semantics <- forAll Gen.bool
  let rhsInner = mkIterAppNoAnn (builtin () PLC.XorByteString) [
        mkConstant @Bool () semantics,
        mkConstant @ByteString () bs,
        mkConstant @ByteString () bs
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
        rhsInner
        ]
  evaluateAndVerify (mkConstant @Integer () 0) rhs

-- | There should exist a monoid homomorphism between natural number addition and function composition for
-- shifts over a fixed bytestring argument.
shiftHomomorphism :: [TestTree]
shiftHomomorphism = [
  testPropertyNamed "zero shift is identity" "zero_shift_id" idProp,
  -- Because the homomorphism on shifts is more restrictive than on rotations (namely, it is for
  -- naturals and their negative equivalents, not integers), we separate the composition property
  -- into two: one dealing with non-negative, the other with non-positive. This helps a bit with
  -- coverage, as otherwise, we wouldn't necessarily cover both paths equally well, as we'd have to
  -- either discard mismatched signs (which are likely) or 'hack them in-place', which would skew
  -- distributions.
  testPropertyNamed "non-negative addition of shifts is composition" "plus_shift_pos_comp" plusCompProp,
  testPropertyNamed "non-positive addition of shifts is composition" "plus_shift_neg_comp" minusCompProp
  ]
  where
    idProp :: Property
    idProp = property $ do
      bs <- forAllByteString
      let lhs = mkIterAppNoAnn (builtin () PLC.ShiftByteString) [
            mkConstant @ByteString () bs,
            mkConstant @Integer () 0
            ]
      evaluateAndVerify (mkConstant @ByteString () bs) lhs
    plusCompProp :: Property
    plusCompProp = property $ do
      bs <- forAllByteString
      i <- forAll . Gen.integral . Range.linear 0 $ 512
      j <- forAll . Gen.integral . Range.linear 0 $ 512
      let lhsInner = mkIterAppNoAnn (builtin () PLC.AddInteger) [
            mkConstant @Integer () i,
            mkConstant @Integer () j
            ]
      let lhs = mkIterAppNoAnn (builtin () PLC.ShiftByteString) [
            mkConstant @ByteString () bs,
            lhsInner
            ]
      let rhsInner = mkIterAppNoAnn (builtin () PLC.ShiftByteString) [
            mkConstant @ByteString () bs,
            mkConstant @Integer () i
            ]
      let rhs = mkIterAppNoAnn (builtin () PLC.ShiftByteString) [
            rhsInner,
            mkConstant @Integer () j
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            lhs,
            rhs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp
    minusCompProp :: Property
    minusCompProp = property $ do
      bs <- forAllByteString
      i <- forAll . Gen.integral . Range.linear 0 $ negate 512
      j <- forAll . Gen.integral . Range.linear 0 $ negate 512
      let lhsInner = mkIterAppNoAnn (builtin () PLC.AddInteger) [
            mkConstant @Integer () i,
            mkConstant @Integer () j
            ]
      let lhs = mkIterAppNoAnn (builtin () PLC.ShiftByteString) [
            mkConstant @ByteString () bs,
            lhsInner
            ]
      let rhsInner = mkIterAppNoAnn (builtin () PLC.ShiftByteString) [
            mkConstant @ByteString () bs,
            mkConstant @Integer () i
            ]
      let rhs = mkIterAppNoAnn (builtin () PLC.ShiftByteString) [
            rhsInner,
            mkConstant @Integer () j
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            lhs,
            rhs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp

-- | There should exist a monoid homomorphism between integer addition and function composition for
-- rotations over a fixed bytestring argument.
rotateHomomorphism :: [TestTree]
rotateHomomorphism = [
  testPropertyNamed "zero rotation is identity" "zero_rotate_id" idProp,
  testPropertyNamed "addition of rotations is composition" "plus_rotate_comp" compProp
  ]
  where
    idProp :: Property
    idProp = property $ do
      bs <- forAllByteString
      let lhs = mkIterAppNoAnn (builtin () PLC.RotateByteString) [
            mkConstant @ByteString () bs,
            mkConstant @Integer () 0
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            lhs,
            mkConstant @ByteString () bs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp
    compProp :: Property
    compProp = property $ do
      bs <- forAllByteString
      i <- forAll . Gen.integral . Range.linear (negate 512) $ 512
      j <- forAll . Gen.integral . Range.linear (negate 512) $ 512
      let lhsInner = mkIterAppNoAnn (builtin () PLC.AddInteger) [
            mkConstant @Integer () i,
            mkConstant @Integer () j
            ]
      let lhs = mkIterAppNoAnn (builtin () PLC.RotateByteString) [
            mkConstant @ByteString () bs,
            lhsInner
            ]
      let rhsInner = mkIterAppNoAnn (builtin () PLC.RotateByteString) [
            mkConstant @ByteString () bs,
            mkConstant @Integer () i
            ]
      let rhs = mkIterAppNoAnn (builtin () PLC.RotateByteString) [
            rhsInner,
            mkConstant @Integer () j
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            lhs,
            rhs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp

-- | There should exist a monoid homomorphism between bytestring concatenation and natural number
-- addition.
csbHomomorphism :: [TestTree]
csbHomomorphism = [
  testCase "count of empty is zero" $ do
    let lhs = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
          mkConstant @ByteString () ""
          ]
    case typecheckEvaluateCek def defaultBuiltinCostModelForTesting lhs of
        Left x -> assertFailure . show $ x
        Right (res, logs) -> case res of
          PLC.EvaluationFailure   -> assertFailure . show $ logs
          PLC.EvaluationSuccess r -> assertEqual "" r (mkConstant @Integer () 0),
  testPropertyNamed "count of concat is addition" "concat_count_plus" compProp
  ]
  where
    compProp :: Property
    compProp = property $ do
      bs1 <- forAllByteString
      bs2 <- forAllByteString
      let lhsInner = mkIterAppNoAnn (builtin () PLC.AppendByteString) [
            mkConstant @ByteString () bs1,
            mkConstant @ByteString () bs2
            ]
      let lhs = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
            lhsInner
            ]
      let rhsLeft = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
            mkConstant @ByteString () bs1
            ]
      let rhsRight = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
            mkConstant @ByteString () bs2
            ]
      let rhs = mkIterAppNoAnn (builtin () PLC.AddInteger) [
            rhsLeft,
            rhsRight
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsInteger) [
            lhs,
            rhs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp

-- | Shifting by more than the bit length (either positive or negative) clears the result.
shiftClear :: Property
shiftClear = property $ do
  bs <- forAllByteString
  let bitLen = 8 * BS.length bs
  i <- forAll . Gen.integral . Range.linear (negate 256) $ 256
  adjustment <- case signum i of
    (-1) -> pure $ negate bitLen + i
    -- Here, we shift by the length exactly, so we randomly pick negative or positive
    0    -> forAll . Gen.element $ [bitLen, negate bitLen]
    _    -> pure $ bitLen + i
  let lhs = mkIterAppNoAnn (builtin () PLC.ShiftByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () (fromIntegral adjustment)
        ]
  let rhsInner = mkIterAppNoAnn (builtin () PLC.LengthOfByteString) [
        mkConstant @ByteString () bs
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.ReplicateByte) [
        rhsInner,
        mkConstant @Integer () 0
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
        lhs,
        rhs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

-- | Positive shifts clear low-index bits.
shiftPosClearLow :: Property
shiftPosClearLow = property $ do
  bs <- forAllByteString1
  let bitLen = 8 * BS.length bs
  n <- forAll . Gen.integral . Range.linear 1 $ bitLen - 1
  i <- forAll . Gen.integral . Range.linear 0 $ n - 1
  let lhsInner = mkIterAppNoAnn (builtin () PLC.ShiftByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () (fromIntegral n)
        ]
  let lhs = mkIterAppNoAnn (builtin () PLC.ReadBit) [
        lhsInner,
        mkConstant @Integer () (fromIntegral i)
        ]
  evaluateAndVerify (mkConstant @Bool () False) lhs

-- | Negative shifts clear high-index bits.
shiftNegClearHigh :: Property
shiftNegClearHigh = property $ do
  bs <- forAllByteString1
  let bitLen = 8 * BS.length bs
  n <- forAll . Gen.integral . Range.linear 1 $ bitLen - 1
  i <- forAll . Gen.integral . Range.linear 0 $ n - 1
  let lhsInner = mkIterAppNoAnn (builtin () PLC.ShiftByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () (fromIntegral . negate $ n)
        ]
  let lhs = mkIterAppNoAnn (builtin () PLC.ReadBit) [
        lhsInner,
        mkConstant @Integer () (fromIntegral $ bitLen - i - 1)
        ]
  evaluateAndVerify (mkConstant @Bool () False) lhs

-- | Rotations by more than the bit length 'roll over' bits.
rotateRollover :: Property
rotateRollover = property $ do
  bs <- forAllByteString
  let bitLen = 8 * BS.length bs
  i <- forAll . Gen.integral . Range.linear (negate 512) $ 512
  let lhs = mkIterAppNoAnn (builtin () PLC.RotateByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () (case signum i of
                                  (-1) -> (negate . fromIntegral $ bitLen) + i
                                  _    -> fromIntegral bitLen + i)
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.RotateByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () i
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
        lhs,
        rhs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

-- | Rotations move bits, but don't change them.
rotateMoveBits :: Property
rotateMoveBits = property $ do
  bs <- forAllByteString1
  let bitLen = 8 * BS.length bs
  i <- forAll . Gen.integral . Range.linear 0 $ bitLen - 1
  j <- forAll . Gen.integral . Range.linear (negate 256) $ 256
  let lhs = mkIterAppNoAnn (builtin () PLC.ReadBit) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () (fromIntegral i)
        ]
  let rhsRotation = mkIterAppNoAnn (builtin () PLC.RotateByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () (fromIntegral j)
        ]
  let rhsIndex = mkIterAppNoAnn (builtin () PLC.ModInteger) [
        mkConstant @Integer () (fromIntegral $ i + j),
        mkConstant @Integer () (fromIntegral bitLen)
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.ReadBit) [
        rhsRotation,
        rhsIndex
        ]
  evaluateTheSame lhs rhs

-- | Rotations do not change how many set (and clear) bits there are.
csbRotate :: Property
csbRotate = property $ do
  bs <- forAllByteString
  i <- forAll . Gen.integral . Range.linear (negate 512) $ 512
  let lhs = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
        mkConstant @ByteString () bs
        ]
  let rhsInner = mkIterAppNoAnn (builtin () PLC.RotateByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () i
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
        rhsInner
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsInteger) [
        lhs,
        rhs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

-- Helpers

forAllByteString :: PropertyT IO ByteString
forAllByteString = forAllWith hexShow . Gen.bytes . Range.linear 0 $ 1024

forAllByteString1 :: PropertyT IO ByteString
forAllByteString1 = forAllWith hexShow . Gen.bytes . Range.linear 1 $ 1024

forAllNonZeroByteString :: PropertyT IO ByteString
forAllNonZeroByteString =
  forAllWith hexShow . Gen.filterT (BS.any (/= 0x00)) . Gen.bytes . Range.linear 0 $ 1024

evaluateAndVerify ::
  UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun () ->
  PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun () ->
  PropertyT IO ()
evaluateAndVerify expected actual =
  case typecheckEvaluateCek def defaultBuiltinCostModelForTesting actual of
    Left x -> annotateShow x >> failure
    Right (res, logs) -> case res of
      PLC.EvaluationFailure   -> annotateShow logs >> failure
      PLC.EvaluationSuccess r -> r === expected

evaluateTheSame ::
  PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun () ->
  PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun () ->
  PropertyT IO ()
evaluateTheSame lhs rhs =
  case typecheckEvaluateCek def defaultBuiltinCostModelForTesting lhs of
    Left x -> annotateShow x >> failure
    Right (resLhs, logsLhs) -> case typecheckEvaluateCek def defaultBuiltinCostModelForTesting rhs of
      Left x -> annotateShow x >> failure
      Right (resRhs, logsRhs) -> case (resLhs, resRhs) of
        (PLC.EvaluationFailure, PLC.EvaluationFailure) -> do
          annotateShow logsLhs
          annotateShow logsRhs
          failure
        (PLC.EvaluationSuccess rLhs, PLC.EvaluationSuccess rRhs) -> rLhs === rRhs
        (PLC.EvaluationFailure, _) -> annotateShow logsLhs >> failure
        (_, PLC.EvaluationFailure) -> annotateShow logsRhs >> failure

hexShow :: ByteString -> String
hexShow = ("0x" <>) . BS.foldl' (\acc w8 -> acc <> byteToHex w8) ""
  where
    byteToHex :: Word8 -> String
    byteToHex w8
      | w8 < 128 = "0" <> showHex w8 ""
      | otherwise = showHex w8 ""
