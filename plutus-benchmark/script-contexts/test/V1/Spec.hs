{-# LANGUAGE OverloadedStrings #-}

module V1.Spec (allTests) where

import Data.Text qualified as Text

import Test.Tasty
import Test.Tasty.Extras (TestNested, ignoreThisTestIfHpcIsEnabled, runTestNested, testNestedGhc)
import Test.Tasty.HUnit

import PlutusBenchmark.Common (Term, compiledCodeToTerm, runTermCek, unsafeRunTermCek)
import PlutusBenchmark.V1.Data.ScriptContexts qualified as Data.SC
import PlutusBenchmark.V1.ScriptContexts qualified as SOP.SC

import PlutusCore.Evaluation.Result
import PlutusCore.Pretty
import PlutusTx.Test qualified as Tx

-- Make a set of golden tests with results stored in subdirectories determined
-- by the GHC version.
runTestGhcSOP :: [TestNested] -> TestTree
runTestGhcSOP = runTestNested ["script-contexts", "test", "V1"] . pure . testNestedGhc

runTestGhcData :: [TestNested] -> TestTree
runTestGhcData = runTestNested ["script-contexts", "test", "V1", "Data"] . pure . testNestedGhc

assertSucceeded :: Term -> Assertion
assertSucceeded t =
    case runTermCek t of
        (Right _, _)  -> pure ()
        (Left err, logs) -> assertFailure . Text.unpack . Text.intercalate "\n" $
            [ render (prettyPlcClassicSimple err)
            , "Cek logs:"
            ] ++ logs

assertFailed :: Term -> Assertion
assertFailed t =
    -- Using `unsafeRunTermCek` here, so that only user errors make the test pass.
    -- Machine errors still make the test fail.
    case unsafeRunTermCek t of
        EvaluationFailure   -> pure ()
        EvaluationSuccess _ -> assertFailure "Evaluation succeeded unexpectedly"

testCheckSOPSc1 :: TestTree
testCheckSOPSc1 = testGroup "checkScriptContext1"
    [ testCase "succeed on 4" . assertSucceeded $
        compiledCodeToTerm $ SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 4)
    , testCase "fails on 5" . assertFailed $
        compiledCodeToTerm $ SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 5)
    , ignoreThisTestIfHpcIsEnabled $
          runTestGhcSOP
               [
                    Tx.goldenSize "checkScriptContext1" $
                        SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 1)
                   , Tx.goldenPirReadable "checkScriptContext1" $
                        SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 1)
                   , Tx.goldenBudget "checkScriptContext1-4" $
                        SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 4)
                   , Tx.goldenEvalCekCatch "checkScriptContext1-4" $
                        [SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 4)]
                   , Tx.goldenBudget "checkScriptContext1-20" $
                        SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 20)
                   , Tx.goldenEvalCekCatch "checkScriptContext1-20" $
                        [SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 20)]
               ]
    ]

testCheckDataSc1 :: TestTree
testCheckDataSc1 = testGroup "checkScriptContext1"
    [ testCase "succeed on 4" . assertSucceeded $
        compiledCodeToTerm $ Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 4)
    , testCase "fails on 5" . assertFailed $
        compiledCodeToTerm $ Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 5)
    , runTestGhcData [ Tx.goldenSize "checkScriptContext1" $
                        Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 1)
                   , Tx.goldenPirReadable "checkScriptContext1" $
                        Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 1)
                   , Tx.goldenBudget "checkScriptContext1-4" $
                        Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 4)
                   , Tx.goldenEvalCekCatch "checkScriptContext1-4" $
                        [Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 4)]
                   , Tx.goldenBudget "checkScriptContext1-20" $
                        Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 20)
                   , Tx.goldenEvalCekCatch "checkScriptContext1-20" $
                        [Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 20)]
          ]
    ]

testCheckSOPSc2 :: TestTree
testCheckSOPSc2 = testGroup "checkScriptContext2"
    [ testCase "succeed on 4" . assertSucceeded $
          compiledCodeToTerm $ SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 4)
    , testCase "succeed on 5" . assertSucceeded $
          compiledCodeToTerm $ SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 5)
    , ignoreThisTestIfHpcIsEnabled $
          runTestGhcSOP
               [ Tx.goldenSize "checkScriptContext2" $
                    SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 1)
               , Tx.goldenPirReadable "checkScriptContext2" $
                    SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 1)
               , Tx.goldenBudget "checkScriptContext2-4" $
                    SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 4)
               , Tx.goldenEvalCekCatch "checkScriptContext2-4" $
                    [SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 4)]
               , Tx.goldenBudget "checkScriptContext2-20" $
                    SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 20)
               , Tx.goldenEvalCekCatch "checkScriptContext2-20" $
                    [SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 20)]
               ]
    ]

testCheckDataSc2 :: TestTree
testCheckDataSc2 = testGroup "checkScriptContext2"
    [ testCase "succeed on 4" . assertSucceeded $
          compiledCodeToTerm $ Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 4)
    , testCase "succeed on 5" . assertSucceeded $
          compiledCodeToTerm $ Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 5)
    , runTestGhcData [ Tx.goldenSize "checkScriptContext2" $
                        Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 1)
                   , Tx.goldenPirReadable "checkScriptContext2" $
                        Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 1)
                   , Tx.goldenBudget "checkScriptContext2-4" $
                        Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 4)
                   , Tx.goldenEvalCekCatch "checkScriptContext2-4" $
                        [Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 4)]
                   , Tx.goldenBudget "checkScriptContext2-20" $
                        Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 20)
                   , Tx.goldenEvalCekCatch "checkScriptContext2-20" $
                        [Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 20)]
                   ]
    ]

testCheckSOPScEquality :: TestTree
testCheckSOPScEquality = testGroup "checkScriptContextEquality"
    [ runTestGhcSOP [ Tx.goldenBudget "checkScriptContextEqualityData-20" $
                        SOP.SC.mkScriptContextEqualityDataCode (SOP.SC.mkScriptContext 20)
                   , Tx.goldenEvalCekCatch "checkScriptContextEqualityData-20" $
                        [SOP.SC.mkScriptContextEqualityDataCode (SOP.SC.mkScriptContext 20)]
                   , Tx.goldenBudget "checkScriptContextEqualityOverhead-20" $
                        SOP.SC.mkScriptContextEqualityOverheadCode (SOP.SC.mkScriptContext 20)
                   , Tx.goldenEvalCekCatch "checkScriptContextEqualityOverhead-20" $
                        [SOP.SC.mkScriptContextEqualityOverheadCode (SOP.SC.mkScriptContext 20)]
                   ]
    ]

testCheckDataScEquality :: TestTree
testCheckDataScEquality = testGroup "checkScriptContextEquality"
    [ runTestGhcData [ Tx.goldenBudget "checkScriptContextEqualityData-20" $
                        Data.SC.mkScriptContextEqualityDataCode (Data.SC.mkScriptContext 20)
                   , Tx.goldenEvalCekCatch "checkScriptContextEqualityData-20" $
                        [Data.SC.mkScriptContextEqualityDataCode (Data.SC.mkScriptContext 20)]
                   , Tx.goldenBudget "checkScriptContextEqualityOverhead-20" $
                        Data.SC.mkScriptContextEqualityOverheadCode (Data.SC.mkScriptContext 20)
                   , Tx.goldenEvalCekCatch "checkScriptContextEqualityOverhead-20" $
                        [Data.SC.mkScriptContextEqualityOverheadCode (Data.SC.mkScriptContext 20)]
                   ]
    ]

allTests :: TestTree
allTests =
  testGroup "plutus-benchmark script-contexts tests"
    [ testCheckSOPSc1
    , testCheckDataSc1
    , testCheckSOPSc2
    , testCheckDataSc2
    , testCheckSOPScEquality
    , testCheckDataScEquality
    ]
