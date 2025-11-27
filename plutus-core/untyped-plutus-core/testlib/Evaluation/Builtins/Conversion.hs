-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Evaluation.Builtins.Conversion
  ( i2bProperty1
  , i2bProperty2
  , i2bProperty3
  , i2bProperty4
  , i2bProperty5
  , i2bProperty6
  , i2bProperty7
  , b2iProperty1
  , b2iProperty2
  , b2iProperty3
  , i2bCipExamples
  , i2bLimitTests
  , b2iCipExamples
  ) where

import Evaluation.Builtins.Common (typecheckEvaluateCek)
import PlutusCore qualified as PLC
import PlutusCore.Bitwise qualified as Bitwise (maximumOutputLength)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModelForTesting)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusPrelude (Word8, def)
import UntypedPlutusCore qualified as UPLC

import Data.ByteString (ByteString)
import GHC.Exts (fromList)
import Hedgehog (Gen, PropertyT, annotateShow, failure, forAllWith, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Text.Show.Pretty (ppShow)

-- Properties and examples directly from CIP-121:
--
-- - https://github.com/cardano-foundation/CIPs/tree/master/CIP-0121#builtinintegertobytestring
-- - https://github.com/cardano-foundation/CIPs/tree/master/CIP-01211#builtinbytestringtointeger

-- lengthOfByteString (integerToByteString e d 0) = d
i2bProperty1 :: PropertyT IO ()
i2bProperty1 = do
  e <- forAllWith ppShow Gen.bool
  -- We limit this temporarily due to the limit imposed on lengths for the
  -- conversion primitive.
  d <- forAllWith ppShow $ Gen.integral (Range.constant 0 Bitwise.maximumOutputLength)
  let actualExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () e
          , mkConstant @Integer () d
          , mkConstant @Integer () 0
          ]
  let lenExp =
        mkIterAppNoAnn
          (builtin () PLC.LengthOfByteString)
          [ actualExp
          ]
  let compareExp =
        mkIterAppNoAnn
          (builtin () PLC.EqualsInteger)
          [ mkConstant @Integer () d
          , lenExp
          ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

-- indexByteString (integerToByteString e k 0) j = 0
i2bProperty2 :: PropertyT IO ()
i2bProperty2 = do
  e <- forAllWith ppShow Gen.bool
  -- We limit this temporarily due to the limit imposed on lengths for the
  -- conversion primitive.
  k <- forAllWith ppShow $ Gen.integral (Range.constant 1 Bitwise.maximumOutputLength)
  j <- forAllWith ppShow $ Gen.integral (Range.constant 0 (k - 1))
  let actualExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () e
          , mkConstant @Integer () k
          , mkConstant @Integer () 0
          ]
  let indexExp =
        mkIterAppNoAnn
          (builtin () PLC.IndexByteString)
          [ actualExp
          , mkConstant @Integer () j
          ]
  evaluateAndVerify (mkConstant @Integer () 0) indexExp

-- lengthOfByteString (integerToByteString e 0 p) > 0
i2bProperty3 :: PropertyT IO ()
i2bProperty3 = do
  e <- forAllWith ppShow Gen.bool
  p <- forAllWith ppShow genP
  let actualExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () e
          , mkConstant @Integer () 0
          , mkConstant @Integer () p
          ]
  let lengthExp =
        mkIterAppNoAnn
          (builtin () PLC.LengthOfByteString)
          [ actualExp
          ]
  let compareExp =
        mkIterAppNoAnn
          (builtin () PLC.LessThanInteger)
          [ mkConstant @Integer () 0
          , lengthExp
          ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

-- integerToByteString False 0 (multiplyInteger p 256) = consByteString
-- 0 (integerToByteString False 0 p)
i2bProperty4 :: PropertyT IO ()
i2bProperty4 = do
  p <- forAllWith ppShow genP
  let pExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () False
          , mkConstant @Integer () 0
          , mkConstant @Integer () p
          ]
  let pTimesExp =
        mkIterAppNoAnn
          (builtin () PLC.MultiplyInteger)
          [ mkConstant @Integer () p
          , mkConstant @Integer () 256
          ]
  let actualExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () False
          , mkConstant @Integer () 0
          , pTimesExp
          ]
  let expectedExp =
        mkIterAppNoAnn
          (builtin () PLC.ConsByteString)
          [ mkConstant @Integer () 0
          , pExp
          ]
  evaluateAndVerify2 expectedExp actualExp

-- integerToByteString True 0 (multiplyInteger p 256) = appendByteString
-- (integerToByteString True 0 p) (singleton 0)
i2bProperty5 :: PropertyT IO ()
i2bProperty5 = do
  p <- forAllWith ppShow genP
  let pExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () True
          , mkConstant @Integer () 0
          , mkConstant @Integer () p
          ]
  let pTimesExp =
        mkIterAppNoAnn
          (builtin () PLC.MultiplyInteger)
          [ mkConstant @Integer () p
          , mkConstant @Integer () 256
          ]
  let actualExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () True
          , mkConstant @Integer () 0
          , pTimesExp
          ]
  let expectedExp =
        mkIterAppNoAnn
          (builtin () PLC.AppendByteString)
          [ pExp
          , mkConstant @ByteString () "\NUL"
          ]
  evaluateAndVerify2 expectedExp actualExp

-- integerToByteString False 0 (plusInteger (multiplyInteger q 256) r) =
-- appendByteString (integerToByteString False 0 r) (integerToByteString False 0 q)
i2bProperty6 :: PropertyT IO ()
i2bProperty6 = do
  q <- forAllWith ppShow genQ
  r <- forAllWith ppShow genR
  let qTimesExp =
        mkIterAppNoAnn
          (builtin () PLC.MultiplyInteger)
          [ mkConstant @Integer () q
          , mkConstant @Integer () 256
          ]
  let largeNumberExp =
        mkIterAppNoAnn
          (builtin () PLC.AddInteger)
          [ qTimesExp
          , mkConstant @Integer () r
          ]
  let actualExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () False
          , mkConstant @Integer () 0
          , largeNumberExp
          ]
  let rBSExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () False
          , mkConstant @Integer () 0
          , mkConstant @Integer () r
          ]
  let qBSExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () False
          , mkConstant @Integer () 0
          , mkConstant @Integer () q
          ]
  let expectedExp =
        mkIterAppNoAnn
          (builtin () PLC.AppendByteString)
          [ rBSExp
          , qBSExp
          ]
  evaluateAndVerify2 expectedExp actualExp

-- integerToByteString True 0 (plusInteger (multiplyInteger q 256) r) =
-- appendByteString (integerToByteString False 0 q)
-- (integerToByteString False 0 r)
i2bProperty7 :: PropertyT IO ()
i2bProperty7 = do
  q <- forAllWith ppShow genQ
  r <- forAllWith ppShow genR
  let qTimesExp =
        mkIterAppNoAnn
          (builtin () PLC.MultiplyInteger)
          [ mkConstant @Integer () q
          , mkConstant @Integer () 256
          ]
  let largeNumberExp =
        mkIterAppNoAnn
          (builtin () PLC.AddInteger)
          [ qTimesExp
          , mkConstant @Integer () r
          ]
  let rBSExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () True
          , mkConstant @Integer () 0
          , mkConstant @Integer () r
          ]
  let qBSExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () True
          , mkConstant @Integer () 0
          , mkConstant @Integer () q
          ]
  let actualExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () True
          , mkConstant @Integer () 0
          , largeNumberExp
          ]
  let expectedExp =
        mkIterAppNoAnn
          (builtin () PLC.AppendByteString)
          [ qBSExp
          , rBSExp
          ]
  evaluateAndVerify2 expectedExp actualExp

-- byteStringToInteger b (integerToByteString b 0 q) = q
b2iProperty1 :: PropertyT IO ()
b2iProperty1 = do
  b <- forAllWith ppShow Gen.bool
  q <- forAllWith ppShow genQ
  let actualExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () b
          , mkConstant @Integer () 0
          , mkConstant @Integer () q
          ]
  let convertedExp =
        mkIterAppNoAnn
          (builtin () PLC.ByteStringToInteger)
          [ mkConstant @Bool () b
          , actualExp
          ]
  evaluateAndVerify (mkConstant @Integer () q) convertedExp

-- byteStringToInteger b (consByteString w8 emptyByteString) = w8
b2iProperty2 :: PropertyT IO ()
b2iProperty2 = do
  w8 :: Integer <- fromIntegral <$> forAllWith ppShow (Gen.enumBounded @_ @Word8)
  b <- forAllWith ppShow Gen.bool
  let consed =
        mkIterAppNoAnn
          (builtin () PLC.ConsByteString)
          [ mkConstant @Integer () w8
          , mkConstant @ByteString () ""
          ]
  let actualExp =
        mkIterAppNoAnn
          (builtin () PLC.ByteStringToInteger)
          [ mkConstant @Bool () b
          , consed
          ]
  evaluateAndVerify (mkConstant @Integer () w8) actualExp

-- integerToByteString b (lengthOfByteString bs) (byteStringToInteger b bs) = bs
b2iProperty3 :: PropertyT IO ()
b2iProperty3 = do
  b <- forAllWith ppShow Gen.bool
  bs <- forAllWith ppShow $ Gen.bytes (Range.linear 0 17)
  let sized =
        mkIterAppNoAnn
          (builtin () PLC.LengthOfByteString)
          [ mkConstant @ByteString () bs
          ]
  let converted =
        mkIterAppNoAnn
          (builtin () PLC.ByteStringToInteger)
          [ mkConstant @Bool () b
          , mkConstant @ByteString () bs
          ]
  let actualExp =
        mkIterAppNoAnn
          (builtin () PLC.IntegerToByteString)
          [ mkConstant @Bool () b
          , sized
          , converted
          ]
  evaluateAndVerify (mkConstant @ByteString () bs) actualExp

i2bCipExamples :: [TestTree]
i2bCipExamples =
  [ -- integerToByteString False 0 (-1) => failure
    testCase
      "example 1"
      ( let actualExp =
              mkIterAppNoAnn
                (builtin () PLC.IntegerToByteString)
                [ mkConstant @Bool () False
                , mkConstant @Integer () 0
                , mkConstant @Integer () (-1)
                ]
         in evaluateShouldFail actualExp
      )
  , -- integerToByteString True 0 (-1) => failure
    testCase "example 2" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () True
              , mkConstant @Integer () 0
              , mkConstant @Integer () (-1)
              ]
       in evaluateShouldFail actualExp
  , -- integerToByteString False 100 (-1) => failure
    testCase "example 3" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () False
              , mkConstant @Integer () 100
              , mkConstant @Integer () (-1)
              ]
       in evaluateShouldFail actualExp
  , -- integerToByteString False 0 0 => [ ]
    testCase "example 4" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () False
              , mkConstant @Integer () 0
              , mkConstant @Integer () 0
              ]
       in evaluateAssertEqual (mkConstant @ByteString () "") actualExp
  , -- integerToByteString True 0 0 => [ ]
    testCase "example 5" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () True
              , mkConstant @Integer () 0
              , mkConstant @Integer () 0
              ]
       in evaluateAssertEqual (mkConstant @ByteString () "") actualExp
  , -- integerToByteString False 5 0 => [ 0x00, 0x00, 0x00, 0x00, 0x00]
    testCase "example 6" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () False
              , mkConstant @Integer () 5
              , mkConstant @Integer () 0
              ]
          expectedExp = mkConstant @ByteString () "\NUL\NUL\NUL\NUL\NUL"
       in evaluateAssertEqual expectedExp actualExp
  , -- integerToByteString True 5 0 => [ 0x00, 0x00, 0x00, 0x00, 0x00]
    testCase "example 7" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () True
              , mkConstant @Integer () 5
              , mkConstant @Integer () 0
              ]
          expectedExp = mkConstant @ByteString () "\NUL\NUL\NUL\NUL\NUL"
       in evaluateAssertEqual expectedExp actualExp
  , -- integerToByteString False 536870912 0 => failure
    testCase "example 8" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () False
              , mkConstant @Integer () 536870912
              , mkConstant @Integer () 0
              ]
       in evaluateShouldFail actualExp
  , -- integerToByteString True 536870912 0 => failure
    testCase "example 9" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () True
              , mkConstant @Integer () 536870912
              , mkConstant @Integer () 0
              ]
       in evaluateShouldFail actualExp
  , -- integerToByteString False 1 404 => failure
    testCase "example 10" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () False
              , mkConstant @Integer () 1
              , mkConstant @Integer () 404
              ]
       in evaluateShouldFail actualExp
  , -- integerToByteString True 1 404 => failure
    testCase "example 11" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () True
              , mkConstant @Integer () 1
              , mkConstant @Integer () 404
              ]
       in evaluateShouldFail actualExp
  , -- integerToByteString False 2 404 => [ 0x94, 0x01 ]
    testCase "example 12" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () False
              , mkConstant @Integer () 2
              , mkConstant @Integer () 404
              ]
          expectedExp = mkConstant @ByteString () (fromList [0x94, 0x01])
       in evaluateAssertEqual expectedExp actualExp
  , -- integerToByteString False 0 404 => [ 0x94, 0x01 ]
    testCase "example 13" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () False
              , mkConstant @Integer () 0
              , mkConstant @Integer () 404
              ]
          expectedExp = mkConstant @ByteString () (fromList [0x94, 0x01])
       in evaluateAssertEqual expectedExp actualExp
  , -- integerToByteString True 2 404 => [ 0x01, 0x94 ]
    testCase "example 14" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () True
              , mkConstant @Integer () 2
              , mkConstant @Integer () 404
              ]
          expectedExp = mkConstant @ByteString () (fromList [0x01, 0x94])
       in evaluateAssertEqual expectedExp actualExp
  , -- integerToByteString True 0 404 => [ 0x01, 0x94 ]
    testCase "example 15" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () True
              , mkConstant @Integer () 0
              , mkConstant @Integer () 404
              ]
          expectedExp = mkConstant @ByteString () (fromList [0x01, 0x94])
       in evaluateAssertEqual expectedExp actualExp
  , -- integerToByteString False 5 404 => [ 0x94, 0x01, 0x00, 0x00, 0x00 ]
    testCase "example 16" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () False
              , mkConstant @Integer () 5
              , mkConstant @Integer () 404
              ]
          expectedExp = mkConstant @ByteString () (fromList [0x94, 0x01, 0x00, 0x00, 0x00])
       in evaluateAssertEqual expectedExp actualExp
  , -- integerToByteString True 5 404 => [ 0x00, 0x00, 0x00, 0x01, 0x94 ]
    testCase "example 17" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.IntegerToByteString)
              [ mkConstant @Bool () True
              , mkConstant @Integer () 5
              , mkConstant @Integer () 404
              ]
          expectedExp = mkConstant @ByteString () (fromList [0x00, 0x00, 0x00, 0x01, 0x94])
       in evaluateAssertEqual expectedExp actualExp
  ]

-- Unit tests to make sure that `integerToByteString` behaves as expected for
-- inputs close to the maximum size.
i2bLimitTests :: [TestTree]
i2bLimitTests =
  let maxAcceptableInput = 2 ^ (8 * Bitwise.maximumOutputLength) - 1
      maxOutput = fromList (take (fromIntegral Bitwise.maximumOutputLength) $ repeat 0xFF)
      makeTests endianness =
        let prefix =
              if endianness
                then "Big-endian, "
                else "Little-endian, "
            mkIntegerToByteStringApp width input =
              mkIterAppNoAnn
                (builtin () PLC.IntegerToByteString)
                [ mkConstant @Bool () endianness
                , mkConstant @Integer () width
                , mkConstant @Integer () input
                ]
         in [ -- integerToByteString 0 maxInput = 0xFF...FF
              testCase (prefix ++ "maximum acceptable input, no length specified") $
                let actualExp = mkIntegerToByteStringApp 0 maxAcceptableInput
                    expectedExp = mkConstant @ByteString () maxOutput
                 in evaluateAssertEqual expectedExp actualExp
            , -- integerToByteString maxLen maxInput = 0xFF...FF
              testCase (prefix ++ "maximum acceptable input, maximum acceptable length argument") $
                let actualExp = mkIntegerToByteStringApp Bitwise.maximumOutputLength maxAcceptableInput
                    expectedExp = mkConstant @ByteString () maxOutput
                 in evaluateAssertEqual expectedExp actualExp
            , -- integerToByteString 0 (maxInput+1) fails
              testCase (prefix ++ "input too big, no length specified") $
                let actualExp = mkIntegerToByteStringApp 0 (maxAcceptableInput + 1)
                 in evaluateShouldFail actualExp
            , -- integerToByteString maxLen (maxInput+1) fails
              testCase (prefix ++ "input too big, maximum acceptable length argument") $
                let actualExp = mkIntegerToByteStringApp Bitwise.maximumOutputLength (maxAcceptableInput + 1)
                 in evaluateShouldFail actualExp
            , -- integerToByteString (maxLen-1) maxInput fails
              testCase (prefix ++ "maximum acceptable input, length argument not big enough") $
                let actualExp = mkIntegerToByteStringApp (Bitwise.maximumOutputLength - 1) maxAcceptableInput
                 in evaluateShouldFail actualExp
            , -- integerToByteString _ (maxLen+1) 0 fails, just to make sure that
              -- we can't go beyond the supposed limit
              testCase (prefix ++ "input zero, length argument over limit") $
                let actualExp = mkIntegerToByteStringApp (Bitwise.maximumOutputLength + 1) 0
                 in evaluateShouldFail actualExp
            ]
   in makeTests True ++ makeTests False

b2iCipExamples :: [TestTree]
b2iCipExamples =
  [ -- byteStringToInteger False emptyByteString => 0
    testCase "example 1" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.ByteStringToInteger)
              [ mkConstant @Bool () False
              , mkConstant @ByteString () ""
              ]
          expectedExp = mkConstant @Integer () 0
       in evaluateAssertEqual expectedExp actualExp
  , -- byteStringToInteger True emptyByteString => 0
    testCase "example 2" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.ByteStringToInteger)
              [ mkConstant @Bool () True
              , mkConstant @ByteString () ""
              ]
          expectedExp = mkConstant @Integer () 0
       in evaluateAssertEqual expectedExp actualExp
  , -- byteStringToInteger False (consByteString 0x01 (consByteString 0x01 emptyByteString)) =>
    -- 257
    testCase "example 3" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.ByteStringToInteger)
              [ mkConstant @Bool () False
              , mkConstant @ByteString () (fromList [0x01, 0x01])
              ]
          expectedExp = mkConstant @Integer () 257
       in evaluateAssertEqual expectedExp actualExp
  , -- byteStringToInteger True (consByteString 0x01 (consByteString 0x01 emptyByteString)) =>
    -- 257
    testCase "example 4" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.ByteStringToInteger)
              [ mkConstant @Bool () True
              , mkConstant @ByteString () (fromList [0x01, 0x01])
              ]
          expectedExp = mkConstant @Integer () 257
       in evaluateAssertEqual expectedExp actualExp
  , -- byteStringToInteger True (consByteString 0x00 (consByteString 0x01 (consByteString 0x01
    -- emptyByteString))) => 257
    testCase "example 5" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.ByteStringToInteger)
              [ mkConstant @Bool () True
              , mkConstant @ByteString () (fromList [0x00, 0x01, 0x01])
              ]
          expectedExp = mkConstant @Integer () 257
       in evaluateAssertEqual expectedExp actualExp
  , -- byteStringToInteger False (consByteString 0x00 (consByteString 0x01 (consByteString 0x01
    -- emptyByteString))) => 65792
    testCase "example 6" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.ByteStringToInteger)
              [ mkConstant @Bool () False
              , mkConstant @ByteString () (fromList [0x00, 0x01, 0x01])
              ]
          expectedExp = mkConstant @Integer () 65792
       in evaluateAssertEqual expectedExp actualExp
  , -- byteStringToInteger False (consByteString 0x01 (consByteString 0x01 (consByteString 0x00
    -- emptyByteString))) => 257
    testCase "example 7" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.ByteStringToInteger)
              [ mkConstant @Bool () False
              , mkConstant @ByteString () (fromList [0x01, 0x01, 0x00])
              ]
          expectedExp = mkConstant @Integer () 257
       in evaluateAssertEqual expectedExp actualExp
  , -- byteStringToInteger True (consByteString 0x01 (consByteString 0x01 (consByteString 0x00
    -- emptyByteString))) => 65792
    testCase "example 8" $
      let actualExp =
            mkIterAppNoAnn
              (builtin () PLC.ByteStringToInteger)
              [ mkConstant @Bool () True
              , mkConstant @ByteString () (fromList [0x01, 0x01, 0x00])
              ]
          expectedExp = mkConstant @Integer () 65792
       in evaluateAssertEqual expectedExp actualExp
  ]

-- Generators

-- As per the CIP, p must be positive, and needs to be large enough to reasonably exercise our
-- tests. We choose a maximum size of 17 bytes: this is enough to give meaningful coverage, but not
-- so large as to slow the tests down excessively.
genP :: Gen Integer
genP = Gen.integral (Range.constant 1 (256 ^ (17 :: Int) - 1))

-- Same as above, except 0 is allowed.
genQ :: Gen Integer
genQ = Gen.integral (Range.constant 0 (256 ^ (17 :: Int) - 1))

genR :: Gen Integer
genR = Gen.integral (Range.constant 1 255)

-- Helpers

evaluateAndVerify
  :: UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> PropertyT IO ()
evaluateAndVerify expected actual =
  case typecheckEvaluateCek def defaultBuiltinCostModelForTesting actual of
    Left x -> annotateShow x >> failure
    Right (res, logs) -> case res of
      PLC.EvaluationFailure -> annotateShow logs >> failure
      PLC.EvaluationSuccess r -> r === expected

evaluateAndVerify2
  :: PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> PropertyT IO ()
evaluateAndVerify2 expected actual =
  let expectedResult = typecheckEvaluateCek def defaultBuiltinCostModelForTesting expected
      actualResult = typecheckEvaluateCek def defaultBuiltinCostModelForTesting actual
   in case (expectedResult, actualResult) of
        (Left err, _) -> annotateShow err >> failure
        (_, Left err) -> annotateShow err >> failure
        (Right (eRes, eLogs), Right (aRes, aLogs)) -> case (eRes, aRes) of
          (PLC.EvaluationFailure, _) -> annotateShow eLogs >> failure
          (_, PLC.EvaluationFailure) -> annotateShow aLogs >> failure
          (PLC.EvaluationSuccess eResult, PLC.EvaluationSuccess aResult) -> eResult === aResult

evaluateShouldFail
  :: PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> IO ()
evaluateShouldFail expr = case typecheckEvaluateCek def defaultBuiltinCostModelForTesting expr of
  Left _ -> assertFailure "unexpectedly failed to typecheck"
  Right (result, _) -> case result of
    PLC.EvaluationFailure -> pure ()
    PLC.EvaluationSuccess _ -> assertFailure "should have failed, but didn't"

evaluateAssertEqual
  :: UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> IO ()
evaluateAssertEqual expected actual =
  case typecheckEvaluateCek def defaultBuiltinCostModelForTesting actual of
    Left _ -> assertFailure "unexpectedly failed to typecheck"
    Right (result, _) -> case result of
      PLC.EvaluationFailure -> assertFailure "unexpectedly failed to evaluate"
      PLC.EvaluationSuccess x -> assertEqual "" x expected
