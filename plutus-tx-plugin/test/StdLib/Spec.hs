{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

module StdLib.Spec where

import Control.DeepSeq (NFData, force)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad.Except (runExceptT)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Proxy (Proxy (..))
import Data.Ratio ((%))
import GHC.Exts (fromString)
import Hedgehog (MonadGen, Property)
import Hedgehog qualified
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore.Data qualified as PLC
import PlutusCore.MkPlc qualified as Core
import PlutusCore.Test (TestNested, embed, runUPlc, testNested, testNestedGhc)
import PlutusPrelude (reoption)
import PlutusTx.Builtins.Internal (BuiltinData (BuiltinData))
import PlutusTx.Code (CompiledCode, getPlcNoAnn)
import PlutusTx.Eq qualified as PlutusTx
import PlutusTx.Lift qualified as Lift
import PlutusTx.Ord qualified as PlutusTx
import PlutusTx.Plugin (plc)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Ratio qualified as Ratio
import PlutusTx.Test (goldenPirReadable)
import Test.Tasty (TestName, TestTree)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

roundPlc :: CompiledCode (Ratio.Rational -> Integer)
roundPlc = plc (Proxy @"roundPlc") Ratio.round

tests :: TestNested
tests =
  testNested "StdLib" . pure $
    testNestedGhc
      [ embed testRatioInterop
      , testRatioProperty "round" Ratio.round round
      , testRatioProperty "truncate" Ratio.truncate truncate
      , testRatioProperty "abs" (fmap Ratio.toHaskellRatio Ratio.abs) abs
      , embed $ testPropertyNamed "ord" "testOrd" testOrd
      , embed $ testPropertyNamed "divMod" "testDivMod" testDivMod
      , embed $ testPropertyNamed "quotRem" "testQuotRem" testQuotRem
      , embed $ testPropertyNamed "Eq @Data" "eqData" eqData
      , goldenPirReadable "errorTrace" errorTrace
      ]

-- We really should use something like "Control.Exception.Enclosed" here and in other similar
-- places.

{-| Evaluate (deeply, to get through tuples) a value, throwing away any exception and just
representing it as 'Nothing'.
-}
tryHard :: (MonadIO m, NFData a) => a -> m (Maybe a)
-- We have @Strict@ enabled, hence without the tilda this function evaluates @a@ before evaluating
-- the body, i.e. outside of the call to 'try', defeating the whole purpose.
tryHard ~a = reoption <$> (liftIO $ try @SomeException $ evaluate $ force a)

testRatioInterop :: TestTree
testRatioInterop = testCase "ratioInterop" do
  runExceptT (runUPlc [getPlcNoAnn roundPlc, snd (Lift.liftProgramDef (Ratio.fromHaskellRatio 3.75))])
    >>= \case
      Left e -> assertFailure (show e)
      Right r -> r @?= Core.mkConstant () (4 :: Integer)

testRatioProperty
  :: (Show a, Eq a) => TestName -> (Ratio.Rational -> a) -> (Rational -> a) -> TestNested
testRatioProperty nm plutusFunc ghcFunc =
  embed $ testPropertyNamed nm (fromString nm) $ Hedgehog.property $ do
    rat <- Hedgehog.forAll $ Gen.realFrac_ (Range.linearFrac (-10000) 100000)
    let ghcResult = ghcFunc rat
        plutusResult = plutusFunc $ Ratio.fromHaskellRatio rat
    Hedgehog.annotateShow ghcResult
    Hedgehog.annotateShow plutusResult
    Hedgehog.assert (ghcResult == plutusResult)

testDivMod :: Property
testDivMod = Hedgehog.property $ do
  -- Generating zeroes often enough to trigger any potential bugs related to handling of zeroes.
  let gen = Gen.frequency [(1, pure 0), (10, Gen.integral (Range.linear (-10000) 100000))]
  (n1, n2) <- Hedgehog.forAll $ (,) <$> gen <*> gen
  ghcResult <- tryHard $ divMod n1 n2
  plutusResult <- tryHard $ PlutusTx.divMod n1 n2
  Hedgehog.annotateShow ghcResult
  Hedgehog.annotateShow plutusResult
  Hedgehog.assert (ghcResult == plutusResult)

testQuotRem :: Property
testQuotRem = Hedgehog.property $ do
  -- Generating zeroes often enough to trigger any potential bugs related to handling of zeroes.
  let gen = Gen.frequency [(1, pure 0), (10, Gen.integral (Range.linear (-10000) 100000))]
  (n1, n2) <- Hedgehog.forAll $ (,) <$> gen <*> gen
  ghcResult <- tryHard $ quotRem n1 n2
  plutusResult <- tryHard $ PlutusTx.quotRem n1 n2
  Hedgehog.annotateShow ghcResult
  Hedgehog.annotateShow plutusResult
  Hedgehog.assert (ghcResult == plutusResult)

testOrd :: Property
testOrd = Hedgehog.property $ do
  let gen = Gen.integral (Range.linear (-10000) 100000)
      -- Ratio must have non-zero denominator or else an ArithException will be thrown.
      gen' = Gen.filter (/= 0) gen
  n1 <- Hedgehog.forAll $ (%) <$> gen <*> gen'
  n2 <- Hedgehog.forAll $ (%) <$> gen <*> gen'
  ghcResult <- tryHard $ n1 <= n2
  plutusResult <- tryHard $ (PlutusTx.<=) (Ratio.fromHaskellRatio n1) (Ratio.fromHaskellRatio n2)
  Hedgehog.annotateShow ghcResult
  Hedgehog.annotateShow plutusResult
  Hedgehog.assert (ghcResult == plutusResult)

eqData :: Property
eqData = Hedgehog.property $ do
  theData <- BuiltinData <$> Hedgehog.forAll genData
  let ghcResult = theData == theData
      plutusResult = theData PlutusTx.== theData
  Hedgehog.annotateShow theData
  Hedgehog.assert (ghcResult && plutusResult)

genData :: (MonadGen m) => m PLC.Data
genData =
  let genInteger = Gen.integral (Range.linear (-10000) 100000)
      genBytes = Gen.bytes (Range.linear 0 1000)
      genList = Gen.list (Range.linear 0 10)
   in Gen.recursive
        Gen.choice
        [ PLC.I <$> genInteger
        , PLC.B <$> genBytes
        ]
        [ PLC.Constr <$> genInteger <*> genList genData
        , PLC.Map <$> genList ((,) <$> genData <*> genData)
        , PLC.List <$> genList genData
        ]

errorTrace :: CompiledCode Integer
errorTrace = plc (Proxy @"errorTrace") (PlutusTx.traceError "")
