{-# LANGUAGE OverloadedStrings #-}

module V3.Spec (allTests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Extras (TestNested, runTestNested, testNestedGhc)
import Test.Tasty.HUnit (testCase)

import PlutusBenchmark.V3.Data.ScriptContexts qualified as Data.SC
import PlutusBenchmark.V3.ScriptContexts qualified as SOP.SC

import PlutusTx.Test qualified as Tx
import PlutusTx.Test.Golden (goldenEvalCekCatchBudget)
import PlutusTx.Test.Run.Code (assertEvaluatesSuccessfully, assertEvaluatesWithError)

-- Make a set of golden tests with results stored in subdirectories determined
-- by the GHC version.
runTestGhcSOP :: [TestNested] -> TestTree
runTestGhcSOP = runTestNested ["script-contexts", "test", "V3"] . pure . testNestedGhc

runTestGhcData :: [TestNested] -> TestTree
runTestGhcData = runTestNested ["script-contexts", "test", "V3", "Data"] . pure . testNestedGhc

testCheckSOPSc1 :: TestTree
testCheckSOPSc1 =
  testGroup
    "checkScriptContext1"
    [ testCase "succeed on 4" . assertEvaluatesSuccessfully $
        SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 4)
    , testCase "fails on 5" . assertEvaluatesWithError $
        SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 5)
    , runTestGhcSOP
        [ Tx.goldenAstSize "checkScriptContext1" $
            SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 1)
        , Tx.goldenPirReadable "checkScriptContext1" $
            SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 1)
        , goldenEvalCekCatchBudget "checkScriptContext1-4" $
            SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 4)
        , goldenEvalCekCatchBudget "checkScriptContext1-20" $
            SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 20)
        ]
    ]

testCheckDataSc1 :: TestTree
testCheckDataSc1 =
  testGroup
    "checkScriptContext1"
    [ testCase "succeed on 4" . assertEvaluatesSuccessfully $
        Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 4)
    , testCase "fails on 5" . assertEvaluatesWithError $
        Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 5)
    , runTestGhcData
        [ Tx.goldenAstSize "checkScriptContext1" $
            Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 1)
        , Tx.goldenPirReadable "checkScriptContext1" $
            Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 1)
        , goldenEvalCekCatchBudget "checkScriptContext1-4" $
            Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 4)
        , goldenEvalCekCatchBudget "checkScriptContext1-20" $
            Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 20)
        ]
    ]

testCheckSOPSc2 :: TestTree
testCheckSOPSc2 =
  testGroup
    "checkScriptContext2"
    [ testCase "succeed on 4" . assertEvaluatesSuccessfully $
        SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 4)
    , testCase "succeed on 5" . assertEvaluatesSuccessfully $
        SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 5)
    , runTestGhcSOP
        [ Tx.goldenAstSize "checkScriptContext2" $
            SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 1)
        , Tx.goldenPirReadable "checkScriptContext2" $
            SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 1)
        , goldenEvalCekCatchBudget "checkScriptContext2-4" $
            SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 4)
        , goldenEvalCekCatchBudget "checkScriptContext2-20" $
            SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 20)
        ]
    ]

testCheckDataSc2 :: TestTree
testCheckDataSc2 =
  testGroup
    "checkScriptContext2"
    [ testCase "succeed on 4" . assertEvaluatesSuccessfully $
        Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 4)
    , testCase "succeed on 5" . assertEvaluatesSuccessfully $
        Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 5)
    , runTestGhcData
        [ Tx.goldenAstSize "checkScriptContext2" $
            Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 1)
        , Tx.goldenPirReadable "checkScriptContext2" $
            Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 1)
        , goldenEvalCekCatchBudget "checkScriptContext2-4" $
            Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 4)
        , goldenEvalCekCatchBudget "checkScriptContext2-20" $
            Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 20)
        ]
    ]

testCheckSOPScEquality :: TestTree
testCheckSOPScEquality =
  testGroup
    "checkScriptContextEquality"
    [ runTestGhcSOP
        [ goldenEvalCekCatchBudget "checkScriptContextEqualityData-20" $
            SOP.SC.mkScriptContextEqualityDataCode (SOP.SC.mkScriptContext 20)
        , goldenEvalCekCatchBudget "checkScriptContextEqualityOverhead-20" $
            SOP.SC.mkScriptContextEqualityOverheadCode (SOP.SC.mkScriptContext 20)
        ]
    ]

testCheckDataScEquality :: TestTree
testCheckDataScEquality =
  testGroup
    "checkScriptContextEquality"
    [ runTestGhcData
        [ goldenEvalCekCatchBudget "checkScriptContextEqualityData-20" $
            Data.SC.mkScriptContextEqualityDataCode (Data.SC.mkScriptContext 20)
        , goldenEvalCekCatchBudget "checkScriptContextEqualityOverhead-20" $
            Data.SC.mkScriptContextEqualityOverheadCode (Data.SC.mkScriptContext 20)
        ]
    ]

testPurposeIsWellFormed :: TestTree
testPurposeIsWellFormed =
  testGroup
    "purposeIsWellFormed"
    [ runTestGhcData
        [ Tx.goldenPirReadable
            "purposeIsWellFormed"
            Data.SC.compiledPurposeIsWellFormed
        , Tx.goldenAstSize
            "purposeIsWellFormed"
            Data.SC.compiledPurposeIsWellFormed
        , goldenEvalCekCatchBudget "purposeIsWellFormed-4" $
            Data.SC.mkPurposeIsWellFormedCode (Data.SC.mkMintingScriptContext 4)
        ]
    ]

allTests :: TestTree
allTests =
  testGroup
    "V3"
    [ testCheckSOPSc1
    , testCheckDataSc1
    , testCheckSOPSc2
    , testCheckDataSc2
    , testCheckSOPScEquality
    , testCheckDataScEquality
    , testPurposeIsWellFormed
    ]
