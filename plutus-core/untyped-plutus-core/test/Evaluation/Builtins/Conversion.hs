-- editorconfig-checker-disable-file

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.Conversion (
  i2bProperty1,
  i2bProperty2,
  i2bProperty3,
  i2bProperty4,
  b2iProperty1,
  b2iProperty2,
  i2bCipExamples,
  b2iCipExamples
  ) where

import Data.ByteString (ByteString)
import Evaluation.Builtins.Common (typecheckEvaluateCek)
import GHC.Exts (fromList)
import Hedgehog (Gen, PropertyT, annotateShow, failure, forAllWith, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore (DefaultFun (ByteStringToInteger, ConsByteString, IndexByteString, IntegerToByteString, LengthOfByteString, LessThanInteger, RemainderInteger, SubtractInteger),
                   EvaluationResult (EvaluationFailure, EvaluationSuccess))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModel)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusPrelude (Word8, def)
import Test.Tasty (TestTree)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
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

-- if k > 0, lengthOfByteString (builtinIntegerToByteString e k i) = k
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

i2bCipExamples :: [TestTree]
i2bCipExamples = [
  -- builtinIntegerToByteString False 0 (-1) => failure
  testCase "example 1" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () False,
                      mkConstant @Integer () 0,
                      mkConstant @Integer () (-1)
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> pure ()
        EvaluationSuccess _ -> assertFailure "should have failed, but didn't",
  -- builtinIntegerToByteString True 0 (-1) => failure
  testCase "example 2" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () True,
                      mkConstant @Integer () 0,
                      mkConstant @Integer () (-1)
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> pure ()
        EvaluationSuccess _ -> assertFailure "should have failed, but didn't",
  -- builtinIntegerToByteString False 100 (-1) => failure
  testCase "example 3" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () False,
                      mkConstant @Integer () 100,
                      mkConstant @Integer () (-1)
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> pure ()
        EvaluationSuccess _ -> assertFailure "should have failed, but didn't",
  -- builtinIntegerToByteString False 0 0 => [ 0x00 ]
  testCase "example 4" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () False,
                      mkConstant @Integer () 0,
                      mkConstant @Integer () 0
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @ByteString () "\NUL"),
  -- builtinIntegerToByteString True 0 0 => [ 0x00 ]
  testCase "example 5" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () True,
                      mkConstant @Integer () 0,
                      mkConstant @Integer () 0
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @ByteString () "\NUL"),
  -- builtinIntegerToByteString False 5 0 => [ 0x00, 0x00, 0x00, 0x00, 0x00]
  testCase "example 6" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () False,
                      mkConstant @Integer () 5,
                      mkConstant @Integer () 0
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @ByteString () "\NUL\NUL\NUL\NUL\NUL"),
  -- builtinIntegerToByteString True 5 0 => [ 0x00, 0x00, 0x00, 0x00, 0x00]
  testCase "example 7" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () True,
                      mkConstant @Integer () 5,
                      mkConstant @Integer () 0
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @ByteString () "\NUL\NUL\NUL\NUL\NUL"),
  -- builtinIntegerToByteString False 1 404 => failure
  testCase "example 8" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () False,
                      mkConstant @Integer () 1,
                      mkConstant @Integer () 404
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> pure ()
        EvaluationSuccess _ -> assertFailure "should have failed, but didn't",
  -- builtinIntegerToByteString True 1 404 => failure
  testCase "example 9" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () True,
                      mkConstant @Integer () 1,
                      mkConstant @Integer () 404
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> pure ()
        EvaluationSuccess _ -> assertFailure "should have failed, but didn't",
  -- builtinIntegerToByteString False 2 404 => [ 0x94, 0x01 ]
  testCase "example 10" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () False,
                      mkConstant @Integer () 2,
                      mkConstant @Integer () 404
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @ByteString () (fromList [0x94, 0x01])),
  -- builtinIntegerToByteString False 0 404 => [ 0x94, 0x01 ]
  testCase "example 11" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () False,
                      mkConstant @Integer () 0,
                      mkConstant @Integer () 404
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @ByteString () (fromList [0x94, 0x01])),
  -- builtinIntegerToByteString True 2 404 => [ 0x01, 0x94 ]
  testCase "example 12" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () True,
                      mkConstant @Integer () 2,
                      mkConstant @Integer () 404
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @ByteString () (fromList [0x01, 0x94])),
  -- builtinIntegerToByteString True 0 404 => [ 0x01, 0x94 ]
  testCase "example 13" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () True,
                      mkConstant @Integer () 0,
                      mkConstant @Integer () 404
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @ByteString () (fromList [0x01, 0x94])),
  -- builtinIntegerToByteString False 5 404 => [ 0x94, 0x01, 0x00, 0x00, 0x00 ]
  testCase "example 14" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () False,
                      mkConstant @Integer () 5,
                      mkConstant @Integer () 404
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @ByteString () (fromList [0x94, 0x01, 0x00, 0x00, 0x00])),
  -- builtinIntegerToByteString True 5 404 => [ 0x00, 0x00, 0x00, 0x01, 0x94 ]
  testCase "example 15" $ do
    let actualExp = mkIterAppNoAnn (builtin () IntegerToByteString) [
                      mkConstant @Bool () True,
                      mkConstant @Integer () 5,
                      mkConstant @Integer () 404
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @ByteString () (fromList [0x00, 0x00, 0x00, 0x01, 0x94]))
  ]

b2iCipExamples :: [TestTree]
b2iCipExamples = [
  -- builtinByteStringToInteger False emptyByteString => failure
  testCase "example 1" $ do
    let actualExp = mkIterAppNoAnn (builtin () ByteStringToInteger) [
                      mkConstant @Bool () False,
                      mkConstant @ByteString () ""
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> pure ()
        EvaluationSuccess _ -> assertFailure "should have failed, but didn't",
  -- builtinByteStringToInteger True emptyByteString => failure
  testCase "example 2" $ do
    let actualExp = mkIterAppNoAnn (builtin () ByteStringToInteger) [
                      mkConstant @Bool () True,
                      mkConstant @ByteString () ""
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> pure ()
        EvaluationSuccess _ -> assertFailure "should have failed, but didn't",
  -- builtinByteStringToInteger False (consByteString 0x01 (consByteString 0x01 emptyByteString)) =>
  -- 257
  testCase "example 3" $ do
    let actualExp = mkIterAppNoAnn (builtin () ByteStringToInteger) [
                      mkConstant @Bool () False,
                      mkConstant @ByteString () (fromList [0x01, 0x01])
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @Integer () 257),
  -- builtinByteStringToInteger True (consByteString 0x01 (consByteString 0x01 emptyByteString)) =>
  -- 257
  testCase "example 4" $ do
    let actualExp = mkIterAppNoAnn (builtin () ByteStringToInteger) [
                      mkConstant @Bool () True,
                      mkConstant @ByteString () (fromList [0x01, 0x01])
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @Integer () 257),
  -- builtinByteStringToInteger True (consByteString 0x00 (consByteString 0x01 (consByteString 0x01
  -- emptyByteString))) => 257
  testCase "example 5" $ do
    let actualExp = mkIterAppNoAnn (builtin () ByteStringToInteger) [
                      mkConstant @Bool () True,
                      mkConstant @ByteString () (fromList [0x00, 0x01, 0x01])
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @Integer () 257),
  -- builtinByteStringToInteger False (consByteString 0x00 (consByteString 0x01 (consByteString 0x01
  -- emptyByteString))) => 65792
  testCase "example 6" $ do
    let actualExp = mkIterAppNoAnn (builtin () ByteStringToInteger) [
                      mkConstant @Bool () False,
                      mkConstant @ByteString () (fromList [0x00, 0x01, 0x01])
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @Integer () 65792),
  -- builtinByteStringToInteger False (consByteString 0x01 (consByteString 0x01 (consByteString 0x00
  -- emptyByteString))) => 257
  testCase "example 7" $ do
    let actualExp = mkIterAppNoAnn (builtin () ByteStringToInteger) [
                      mkConstant @Bool () False,
                      mkConstant @ByteString () (fromList [0x01, 0x01, 0x00])
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @Integer () 257),
  -- builtinByteStringToInteger True (consByteString 0x01 (consByteString 0x01 (consByteString 0x00
  -- emptyByteString))) => 65792
  testCase "example 8" $ do
    let actualExp = mkIterAppNoAnn (builtin () ByteStringToInteger) [
                      mkConstant @Bool () True,
                      mkConstant @ByteString () (fromList [0x01, 0x01, 0x00])
                      ]
    case typecheckEvaluateCek def defaultBuiltinCostModel actualExp of
      Left _ -> assertFailure "unexpectedly failed to typecheck"
      Right (result, _) -> case result of
        EvaluationFailure   -> assertFailure "unexpectedly failed to evaluate"
        EvaluationSuccess x -> assertEqual "" x (mkConstant @Integer () 65792)
  ]

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

