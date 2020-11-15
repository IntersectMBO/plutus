{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}

module StdLib.Spec where

import           Common
import           Data.Ratio                   ((%))
import           GHC.Real                     (reduce)
import           Hedgehog                     (Gen, MonadGen, Property)
import qualified Hedgehog
import qualified Hedgehog.Gen                 as Gen
import qualified Hedgehog.Range               as Range
import           Lib
import           PlcTestUtils
import           Plugin.Lib
import           Test.Tasty                   (TestName)
import           Test.Tasty.Hedgehog          (testProperty)

import           Language.PlutusTx.Data       (Data (..))
import qualified Language.PlutusTx.Data       as Data
import qualified Language.PlutusTx.Eq         as PlutusTx
import qualified Language.PlutusTx.Ord        as PlutusTx
import qualified Language.PlutusTx.Prelude    as PlutusTx
import qualified Language.PlutusTx.Ratio      as Ratio

import           Language.PlutusTx.Code
import qualified Language.PlutusTx.Lift       as Lift
import           Language.PlutusTx.Plugin

import qualified Language.PlutusCore.Builtins as PLC
import qualified Language.PlutusCore.Universe as PLC

import           Data.Proxy

roundPlc :: CompiledCode (Ratio.Rational -> Integer)
roundPlc = plc (Proxy @"roundPlc") Ratio.round

tests :: TestNested
tests =
  testNested "StdLib"
    [ goldenUEval "ratioInterop" [ getPlc roundPlc, Lift.liftProgram (Ratio.fromGHC 3.75) ]
    , testRatioProperty "round" Ratio.round round
    , testRatioProperty "truncate" Ratio.truncate truncate
    , testRatioProperty "abs" (fmap Ratio.toGHC Ratio.abs) abs
    , pure $ testProperty "ord" testOrd
    , pure $ testProperty "quotRem" testQuotRem
    , pure $ testProperty "reduce" testReduce
    , pure $ testProperty "Eq @Data" eqData
    , goldenPir "errorTrace" errorTrace
    ]

testRatioProperty :: (Show a, Eq a) => TestName -> (Ratio.Rational -> a) -> (Rational -> a) -> TestNested
testRatioProperty nm plutusFunc ghcFunc = pure $ testProperty nm $ Hedgehog.property $ do
    rat <- Hedgehog.forAll $ Gen.realFrac_ (Range.linearFrac (-10000) 100000)
    let ghcResult = ghcFunc rat
        plutusResult = plutusFunc $ Ratio.fromGHC rat
    Hedgehog.annotateShow ghcResult
    Hedgehog.annotateShow plutusResult
    Hedgehog.assert (ghcResult == plutusResult)

testQuotRem :: Property
testQuotRem = Hedgehog.property $ do
    let gen = Gen.integral (Range.linear (-10000) 100000)
    (n1, n2) <- Hedgehog.forAll $ (,) <$> gen <*> gen
    let ghcResult = quotRem n1 n2
        plutusResult = Ratio.quotRem n1 n2
    Hedgehog.annotateShow ghcResult
    Hedgehog.annotateShow plutusResult
    Hedgehog.assert (ghcResult == plutusResult)

testReduce :: Property
testReduce = Hedgehog.property $ do
    let gen = Gen.integral (Range.linear (-10000) 100000)
    (n1, n2) <- Hedgehog.forAll $ (,) <$> gen <*> gen
    let ghcResult = reduce n1 n2
        plutusResult = Ratio.toGHC $ Ratio.reduce n1 n2
    Hedgehog.annotateShow ghcResult
    Hedgehog.annotateShow plutusResult
    Hedgehog.assert (ghcResult == plutusResult)

testOrd :: Property
testOrd = Hedgehog.property $ do
    let gen = Gen.integral (Range.linear (-10000) 100000)
    let genNonzero = Gen.filter (\i -> not (i == 0)) gen
    n1 <- Hedgehog.forAll $ (%) <$> gen <*> genNonzero
    n2 <- Hedgehog.forAll $ (%) <$> gen <*> genNonzero
    let ghcResult = n1 <= n2
        plutusResult = (PlutusTx.<=) (Ratio.fromGHC n1) (Ratio.fromGHC n2)
    Hedgehog.annotateShow ghcResult
    Hedgehog.annotateShow plutusResult
    Hedgehog.assert (ghcResult == plutusResult)

eqData :: Property
eqData = Hedgehog.property $ do
    theData <- Hedgehog.forAll genData
    let ghcResult = theData == theData
        plutusResult = theData PlutusTx.== theData
    Hedgehog.annotateShow theData
    Hedgehog.assert (ghcResult && plutusResult)

genData :: MonadGen m => m Data
genData =
    let genInteger = Gen.integral (Range.linear (-10000) 100000)
        genBytes   = Gen.bytes (Range.linear 0 1000)
        genList    = Gen.list (Range.linear 0 10)
    in Gen.recursive
            Gen.choice
            [ I <$> genInteger
            , B <$> genBytes
            ]
            [ Constr <$> genInteger <*> genList genData
            , Map <$> genList ((,) <$> genData <*> genData)
            , List <$> genList genData
            ]

errorTrace :: CompiledCode (Integer)
errorTrace = plc (Proxy @"errorTrace") (PlutusTx.traceError "")
