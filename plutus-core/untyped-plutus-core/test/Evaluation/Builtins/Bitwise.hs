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
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Evaluation.Builtins.Common (typecheckEvaluateCek)
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

shiftHomomorphism :: [TestTree]
shiftHomomorphism = [
  testPropertyNamed "zero shift is identity" "zero_shift_id" idProp,
  testPropertyNamed "non-negative addition of shifts is composition" "plus_shift_pos_comp" plusCompProp,
  testPropertyNamed "non-positive addition of shifts is composition" "plus_shift_neg_comp" minusCompProp
  ]
  where
    idProp :: Property
    idProp = property $ do
      bs <- forAllByteString
      let lhs = mkIterAppNoAnn (builtin () PLC.BitwiseShift) [
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
      let lhs = mkIterAppNoAnn (builtin () PLC.BitwiseShift) [
            mkConstant @ByteString () bs,
            lhsInner
            ]
      let rhsInner = mkIterAppNoAnn (builtin () PLC.BitwiseShift) [
            mkConstant @ByteString () bs,
            mkConstant @Integer () i
            ]
      let rhs = mkIterAppNoAnn (builtin () PLC.BitwiseShift) [
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
      let lhs = mkIterAppNoAnn (builtin () PLC.BitwiseShift) [
            mkConstant @ByteString () bs,
            lhsInner
            ]
      let rhsInner = mkIterAppNoAnn (builtin () PLC.BitwiseShift) [
            mkConstant @ByteString () bs,
            mkConstant @Integer () i
            ]
      let rhs = mkIterAppNoAnn (builtin () PLC.BitwiseShift) [
            rhsInner,
            mkConstant @Integer () j
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            lhs,
            rhs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp

rotateHomomorphism :: [TestTree]
rotateHomomorphism = [
  testPropertyNamed "zero rotation is identity" "zero_rotate_id" idProp,
  testPropertyNamed "addition of rotations is composition" "plus_rotate_comp" compProp
  ]
  where
    idProp :: Property
    idProp = property $ do
      bs <- forAllByteString
      let lhs = mkIterAppNoAnn (builtin () PLC.BitwiseRotate) [
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
      let lhs = mkIterAppNoAnn (builtin () PLC.BitwiseRotate) [
            mkConstant @ByteString () bs,
            lhsInner
            ]
      let rhsInner = mkIterAppNoAnn (builtin () PLC.BitwiseRotate) [
            mkConstant @ByteString () bs,
            mkConstant @Integer () i
            ]
      let rhs = mkIterAppNoAnn (builtin () PLC.BitwiseRotate) [
            rhsInner,
            mkConstant @Integer () j
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            lhs,
            rhs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp

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
  let lhs = mkIterAppNoAnn (builtin () PLC.BitwiseShift) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () (fromIntegral adjustment)
        ]
  let rhsInner = mkIterAppNoAnn (builtin () PLC.LengthOfByteString) [
        mkConstant @ByteString () bs
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.ReplicateByteString) [
        rhsInner,
        mkConstant @Integer () 0
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
        lhs,
        rhs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

shiftPosClearLow :: Property
shiftPosClearLow = property $ do
  bs <- forAllByteString1
  let bitLen = 8 * BS.length bs
  n <- forAll . Gen.integral . Range.linear 1 $ bitLen - 1
  i <- forAll . Gen.integral . Range.linear 0 $ n - 1
  let lhsInner = mkIterAppNoAnn (builtin () PLC.BitwiseShift) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () (fromIntegral n)
        ]
  let lhs = mkIterAppNoAnn (builtin () PLC.ReadBit) [
        lhsInner,
        mkConstant @Integer () (fromIntegral i)
        ]
  evaluateAndVerify (mkConstant @Bool () False) lhs

shiftNegClearHigh :: Property
shiftNegClearHigh = property $ do
  bs <- forAllByteString1
  let bitLen = 8 * BS.length bs
  n <- forAll . Gen.integral . Range.linear 1 $ bitLen - 1
  i <- forAll . Gen.integral . Range.linear 0 $ n - 1
  let lhsInner = mkIterAppNoAnn (builtin () PLC.BitwiseShift) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () (fromIntegral . negate $ n)
        ]
  let lhs = mkIterAppNoAnn (builtin () PLC.ReadBit) [
        lhsInner,
        mkConstant @Integer () (fromIntegral $ bitLen - i - 1)
        ]
  evaluateAndVerify (mkConstant @Bool () False) lhs

rotateRollover :: Property
rotateRollover = property $ do
  bs <- forAllByteString
  let bitLen = 8 * BS.length bs
  i <- forAll . Gen.integral . Range.linear (negate 512) $ 512
  let lhs = mkIterAppNoAnn (builtin () PLC.BitwiseRotate) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () (case signum i of
                                  (-1) -> (negate . fromIntegral $ bitLen) + i
                                  _    -> fromIntegral bitLen + i)
        ]
  let rhs = mkIterAppNoAnn (builtin () PLC.BitwiseRotate) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () i
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
        lhs,
        rhs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

csbRotate :: Property
csbRotate = property $ do
  bs <- forAllByteString
  i <- forAll . Gen.integral . Range.linear (negate 512) $ 512
  let lhs = mkIterAppNoAnn (builtin () PLC.CountSetBits) [
        mkConstant @ByteString () bs
        ]
  let rhsInner = mkIterAppNoAnn (builtin () PLC.BitwiseRotate) [
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

hexShow :: ByteString -> String
hexShow = ("0x" <>) . BS.foldl' (\acc w8 -> acc <> byteToHex w8) ""
  where
    byteToHex :: Word8 -> String
    byteToHex w8
      | w8 < 128 = "0" <> showHex w8 ""
      | otherwise = showHex w8 ""
