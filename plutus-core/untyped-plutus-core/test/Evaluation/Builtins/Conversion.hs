-- editorconfig-checker-disable-file

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.Conversion (
  i2bProperty1,
  i2bProperty2,
  i2bProperty3,
  i2bProperty4,
  b2iProperty1,
  b2iProperty2
  ) where

import Data.ByteString (ByteString)
import Evaluation.Builtins.Common (typecheckEvaluateCek)
import Hedgehog (Gen, PropertyT, annotateShow, failure, forAllWith, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore (DefaultFun (ByteStringToInteger, ConsByteString, IndexByteString, IntegerToByteString, LengthOfByteString, LessThanInteger, RemainderInteger, SubtractInteger),
                   EvaluationResult (EvaluationFailure, EvaluationSuccess))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModel)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusPrelude (Word8, def)
import Text.Show.Pretty (ppShow)

-- Properties directly from CIP-0087: https://github.com/mlabs-haskell/CIPs/blob/koz/to-from-bytestring/CIP-0087/CIP-0087.md#builtinintegertobytestring

-- lengthOfByteString (builtinIntegerToByteString e 0 i) > 0
i2bProperty1 :: PropertyT IO ()
i2bProperty1 = do
  e <- forAllWith ppShow Gen.bool
  i <- forAllWith ppShow $ Gen.integral (Range.constant 0 (256 ^ (17 :: Int) - 1))
  let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
        mkConstant @Bool () e,
        mkConstant @Integer () 0,
        mkConstant @Integer () i
        ]
  let lenExp = mkIterAppNoAnn (builtin () LengthOfByteString) [
        actualExp
        ]
  let compareExp = mkIterAppNoAnn (builtin () LessThanInteger) [
        mkConstant @Integer () 0,
        lenExp
        ]
  let result = typecheckEvaluateCek def defaultBuiltinCostModel compareExp
  case result of
    Left x -> annotateShow x >> failure
    Right (res, logs) -> case res of
      EvaluationFailure   -> annotateShow logs >> failure
      EvaluationSuccess r -> r === mkConstant () True

-- lengthOfByteString (builtinIntegerToByteString e k i) = k
i2bProperty2 :: PropertyT IO ()
i2bProperty2 = do
  e <- forAllWith ppShow Gen.bool
  (k, i) <- forAllWith ppShow genProp2Data
  let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
        mkConstant @Bool () e,
        mkConstant @Integer () k,
        mkConstant @Integer () i
        ]
  let lenExp = mkIterAppNoAnn (builtin () LengthOfByteString) [
        actualExp
        ]
  let result = typecheckEvaluateCek def defaultBuiltinCostModel lenExp
  case result of
    Left x -> annotateShow x >> failure
    Right (res, logs) -> case res of
      EvaluationFailure   -> annotateShow logs >> failure
      EvaluationSuccess r -> r === mkConstant @Integer () k

-- indexByteString (builtinIntegerToByteString False d i) 0 = remainderInteger i 256
i2bProperty3 :: PropertyT IO ()
i2bProperty3 = do
  (d, i) <- forAllWith ppShow genProp3Prop4Data
  let expectedExp = mkIterAppNoAnn (builtin () RemainderInteger) [
        mkConstant @Integer () i,
        mkConstant @Integer () 256
        ]
  let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
        mkConstant @Bool () False,
        mkConstant @Integer () d,
        mkConstant @Integer () i
        ]
  let indexExp = mkIterAppNoAnn (builtin () IndexByteString) [
        actualExp,
        mkConstant @Integer () 0
        ]
  let expectedResult = typecheckEvaluateCek def defaultBuiltinCostModel expectedExp
  let actualResult = typecheckEvaluateCek def defaultBuiltinCostModel indexExp
  case (expectedResult, actualResult) of
    (Left err, _) -> annotateShow err >> failure
    (_, Left err) -> annotateShow err >> failure
    (Right (eRes, eLogs), Right (aRes, aLogs)) -> case (eRes, aRes) of
      (EvaluationFailure, _)                                 -> annotateShow eLogs >> failure
      (_, EvaluationFailure)                                 -> annotateShow aLogs >> failure
      (EvaluationSuccess eResult, EvaluationSuccess aResult) -> eResult === aResult

-- let result = builtinIntegerToByteString True d i
-- in indexByteString result (lengthOfByteString result - 1) = remainderInteger i 256
i2bProperty4 :: PropertyT IO ()
i2bProperty4 = do
  (d, i) <- forAllWith ppShow genProp3Prop4Data
  let expectedExp = mkIterAppNoAnn (builtin () RemainderInteger) [
        mkConstant @Integer () i,
        mkConstant @Integer () 256
        ]
  let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
        mkConstant @Bool () True,
        mkConstant @Integer () d,
        mkConstant @Integer () i
        ]
  let lenExp = mkIterAppNoAnn (builtin () LengthOfByteString) [
        actualExp
        ]
  let limitExp = mkIterAppNoAnn (builtin () SubtractInteger) [
        lenExp,
        mkConstant @Integer () 1
        ]
  let indexExp = mkIterAppNoAnn (builtin () IndexByteString) [
        actualExp,
        limitExp
        ]
  let expectedResult = typecheckEvaluateCek def defaultBuiltinCostModel expectedExp
  let actualResult = typecheckEvaluateCek def defaultBuiltinCostModel indexExp
  case (expectedResult, actualResult) of
    (Left err, _) -> annotateShow err >> failure
    (_, Left err) -> annotateShow err >> failure
    (Right (eRes, eLogs), Right (aRes, aLogs)) -> case (eRes, aRes) of
      (EvaluationFailure, _)                                 -> annotateShow eLogs >> failure
      (_, EvaluationFailure)                                 -> annotateShow aLogs >> failure
      (EvaluationSuccess eResult, EvaluationSuccess aResult) -> eResult === aResult

-- builtinByteStringToInteger b (builtinIntegerToByteString b d i) = i
b2iProperty1 :: PropertyT IO ()
b2iProperty1 = do
  b <- forAllWith ppShow Gen.bool
  (d, i) <- forAllWith ppShow genProp3Prop4Data
  let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
        mkConstant @Bool () b,
        mkConstant @Integer () d,
        mkConstant @Integer () i
        ]
  let convertedExp = mkIterAppNoAnn (builtin () ByteStringToInteger) [
        mkConstant @Bool () b,
        actualExp
        ]
  let result = typecheckEvaluateCek def defaultBuiltinCostModel convertedExp
  case result of
    Left err -> annotateShow err >> failure
    Right (res, logs) -> case res of
      EvaluationFailure   -> annotateShow logs >> failure
      EvaluationSuccess x -> x === mkConstant @Integer () i

-- builtinByteStringToInteger b (consByteString w8 emptyByteString) = w8
b2iProperty2 :: PropertyT IO ()
b2iProperty2 = do
  w8 :: Integer <- fromIntegral <$> forAllWith ppShow (Gen.enumBounded @_ @Word8)
  b <- forAllWith ppShow Gen.bool
  let consed = mkIterAppNoAnn (builtin () ConsByteString) [
        mkConstant @Integer () w8,
        mkConstant @ByteString () ""
        ]
  let actualExp = mkIterAppNoAnn (builtin () ByteStringToInteger) [
        mkConstant @Bool () b,
        consed
        ]
  let result = typecheckEvaluateCek def defaultBuiltinCostModel actualExp
  case result of
    Left err -> annotateShow err >> failure
    Right (res, logs) -> case res of
      EvaluationFailure   -> annotateShow logs >> failure
      EvaluationSuccess x -> x === mkConstant @Integer () w8

-- Generators

-- For Property 2 of the Integer -> ByteString direction, we have to be careful when selecting
-- parameters k and i. If we were to pick them completely at random, it is quite likely that we
-- would request a k that is too low to represent i, causing the builtin to error. To avoid this
-- problem, we first select k, then generate an i that can be represented using k digits.
genProp2Data :: Gen (Integer, Integer)
genProp2Data = do
  -- k must be at least 1, or Property 2 doesn't really work
  k <- Gen.integral (Range.constant 1 17)
  i <- Gen.integral (Range.constant 0 (256 ^ k - 1))
  pure (k, i)

-- Properties 3 and 4 of the Integer -> ByteString direction, as well as Property 1 of the
-- ByteString -> Integer direction, have similar requirements for
-- parameters d and i as Property 2 has for parameters k and i. Unlike Property 2,  these allow d to
-- be 0, in which case, i can be freely chosen.
genProp3Prop4Data :: Gen (Integer, Integer)
genProp3Prop4Data = do
  -- d can be 0
  d <- Gen.integral (Range.constant 0 17)
  i <- if d == 0
       then Gen.integral (Range.constant 0 (256 ^ (17 :: Int) - 1))
       else Gen.integral (Range.constant 0 (256 ^ d - 1))
  pure (d, i)

