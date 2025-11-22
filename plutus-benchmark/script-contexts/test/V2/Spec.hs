{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module V2.Spec (allTests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Extras (TestNested, runTestNested, testNestedGhc)
import Test.Tasty.HUnit (testCase)

import PlutusBenchmark.V2.Data.ScriptContexts qualified as Data.SC
import PlutusBenchmark.V2.ScriptContexts qualified as SOP.SC

import PlutusTx qualified
import PlutusTx.Plugin ()
import PlutusTx.Test qualified as Tx
import PlutusTx.Test.Run.Code (assertEvaluatesSuccessfully, assertEvaluatesWithError)

-- Make a set of golden tests with results stored in subdirectories determined
-- by the GHC version.
runTestGhcSOP :: [TestNested] -> TestTree
runTestGhcSOP = runTestNested ["script-contexts", "test", "V2"] . pure . testNestedGhc

runTestGhcData :: [TestNested] -> TestTree
runTestGhcData = runTestNested ["script-contexts", "test", "V2", "Data"] . pure . testNestedGhc

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
        , Tx.goldenEvalCekCatchBudget "checkScriptContext1-4" $
            SOP.SC.mkCheckScriptContext1Code (SOP.SC.mkScriptContext 4)
        , Tx.goldenEvalCekCatchBudget "checkScriptContext1-20" $
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
        , Tx.goldenEvalCekCatchBudget "checkScriptContext1-4" $
            Data.SC.mkCheckScriptContext1Code (Data.SC.mkScriptContext 4)
        , Tx.goldenEvalCekCatchBudget "checkScriptContext1-20" $
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
        , Tx.goldenEvalCekCatchBudget "checkScriptContext2-4" $
            SOP.SC.mkCheckScriptContext2Code (SOP.SC.mkScriptContext 4)
        , Tx.goldenEvalCekCatchBudget "checkScriptContext2-20" $
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
        , Tx.goldenEvalCekCatchBudget "checkScriptContext2-4" $
            Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 4)
        , Tx.goldenEvalCekCatchBudget "checkScriptContext2-20" $
            Data.SC.mkCheckScriptContext2Code (Data.SC.mkScriptContext 20)
        ]
    ]

testCheckSOPScEquality :: TestTree
testCheckSOPScEquality =
  testGroup
    "checkScriptContextEquality"
    [ runTestGhcSOP
        [ Tx.goldenEvalCekCatchBudget "checkScriptContextEqualityData-20" $
            SOP.SC.mkScriptContextEqualityDataCode (SOP.SC.mkScriptContext 20)
        , Tx.goldenEvalCekCatchBudget "checkScriptContextEqualityOverhead-20" $
            SOP.SC.mkScriptContextEqualityOverheadCode (SOP.SC.mkScriptContext 20)
        ]
    ]

testCheckDataScEquality :: TestTree
testCheckDataScEquality =
  testGroup
    "checkScriptContextEquality"
    [ runTestGhcData
        [ Tx.goldenEvalCekCatchBudget "checkScriptContextEqualityData-20" $
            Data.SC.mkScriptContextEqualityDataCode (Data.SC.mkScriptContext 20)
        , Tx.goldenEvalCekCatchBudget "checkScriptContextEqualityOverhead-20" $
            Data.SC.mkScriptContextEqualityOverheadCode (Data.SC.mkScriptContext 20)
        ]
    ]

testSOPFwdStakeTrick :: TestTree
testSOPFwdStakeTrick =
  runTestGhcSOP
    [ Tx.goldenPirReadable "sopFwdStakeTrick" testAbsCode
    , Tx.goldenUPlcReadable "sopFwdStakeTrick" testAbsCode
    , Tx.goldenEvalCekCatchBudget "sopFwdStakeTrick" testCode
    ]
  where
    testCredential =
      SOP.SC.mkStakingCredential "someCredential"
    testScriptContext =
      SOP.SC.mkScriptContextWithStake 20 20 (Just (testCredential, 1))
    testAbsCode =
      $$(PlutusTx.compile [||SOP.SC.forwardWithStakeTrick||])
    testCode =
      SOP.SC.mkForwardWithStakeTrickCode testCredential testScriptContext

testDataFwdStakeTrick :: TestTree
testDataFwdStakeTrick =
  runTestGhcSOP
    [ Tx.goldenPirReadable "dataFwdStakeTrick" testAbsCode
    , Tx.goldenUPlcReadable "dataFwdStakeTrick" testAbsCode
    , Tx.goldenEvalCekCatchBudget "dataFwdStakeTrick" testCode
    ]
  where
    testCredential =
      Data.SC.mkStakingCredential "someCredential"
    testScriptContext =
      Data.SC.mkScriptContextWithStake 20 20 (Just (testCredential, 1))
    testAbsCode =
      $$(PlutusTx.compile [||Data.SC.forwardWithStakeTrick||])
    testCode =
      Data.SC.mkForwardWithStakeTrickCode testCredential testScriptContext

testDataFwdStakeTrickManual :: TestTree
testDataFwdStakeTrickManual =
  runTestGhcSOP
    [ Tx.goldenPirReadable "dataFwdStakeTrickManual" testAbsCode
    , Tx.goldenUPlcReadable "dataFwdStakeTrickManual" testAbsCode
    , Tx.goldenEvalCekCatchBudget "dataFwdStakeTrickManual" testCode
    ]
  where
    testCredential =
      Data.SC.mkStakingCredential "someCredential"
    testScriptContext =
      Data.SC.mkScriptContextWithStake 20 20 (Just (testCredential, 1))
    testAbsCode =
      $$(PlutusTx.compile [||Data.SC.forwardWithStakeTrickManual||])
    testCode =
      Data.SC.mkForwardWithStakeTrickManualCode testCredential testScriptContext

allTests :: TestTree
allTests =
  testGroup
    "V2"
    [ testCheckSOPSc1
    , testCheckDataSc1
    , testCheckSOPSc2
    , testCheckDataSc2
    , testCheckSOPScEquality
    , testCheckDataScEquality
    , testSOPFwdStakeTrick
    , testDataFwdStakeTrick
    , testDataFwdStakeTrickManual
    ]
