{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text qualified as Text

import Test.Tasty
import Test.Tasty.Extras (TestNested, runTestNestedIn)
import Test.Tasty.HUnit

import PlutusBenchmark.Common (Term, compiledCodeToTerm, runTermCek, unsafeRunTermCek)
import PlutusBenchmark.ScriptContexts

import PlutusCore.Evaluation.Result
import PlutusCore.Pretty
import PlutusTx.Test qualified as Tx

runTestNested :: TestNested -> TestTree
runTestNested = runTestNestedIn ["script-contexts", "test"]

assertSucceeded :: Term -> Assertion
assertSucceeded t =
    case runTermCek t of
        (Right _, _)  -> pure ()
        (Left err, logs) -> assertFailure . Text.unpack . Text.intercalate "\n" $
            [ render (prettyPlcClassicDebug err)
            , "Cek logs:"
            ] ++ logs

assertFailed :: Term -> Assertion
assertFailed t =
    -- Using `unsafeRunTermCek` here, so that only user errors make the test pass.
    -- Machine errors still make the test fail.
    case unsafeRunTermCek t of
        EvaluationFailure   -> pure ()
        EvaluationSuccess _ -> assertFailure "Evaluation succeeded unexpectedly"

testCheckSc1 :: TestTree
testCheckSc1 = testGroup "checkScriptContext1"
    [ testCase "succeed on 4" . assertSucceeded $
        compiledCodeToTerm $ mkCheckScriptContext1Code (mkScriptContext 4)
    , testCase "fails on 5" . assertFailed $
        compiledCodeToTerm $ mkCheckScriptContext1Code (mkScriptContext 5)
    , Tx.fitsInto "checkScriptContext1 (size)" (mkCheckScriptContext1Code (mkScriptContext 1)) 3471
    , runTestNested $ Tx.goldenPirReadable "checkScriptContext1" $
        mkCheckScriptContext1Code (mkScriptContext 1)
    , runTestNested $ Tx.goldenBudget "checkScriptContext1-4" $
        mkCheckScriptContext1Code (mkScriptContext 4)
    , runTestNested $ Tx.goldenBudget "checkScriptContext1-20" $
        mkCheckScriptContext1Code (mkScriptContext 20)
    ]

testCheckSc2 :: TestTree
testCheckSc2 = testGroup "checkScriptContext2"
    [ testCase "succeed on 4" . assertSucceeded $
          compiledCodeToTerm $ mkCheckScriptContext2Code (mkScriptContext 4)
    , testCase "succeed on 5" . assertSucceeded $
          compiledCodeToTerm $ mkCheckScriptContext2Code (mkScriptContext 5)
    , Tx.fitsInto "checkScriptContext2 (size)" (mkCheckScriptContext2Code (mkScriptContext 1)) 3402
    , runTestNested $ Tx.goldenPirReadable "checkScriptContext2" $
          mkCheckScriptContext2Code (mkScriptContext 1)
    , runTestNested $ Tx.goldenBudget "checkScriptContext2-4" $
          mkCheckScriptContext2Code (mkScriptContext 4)
    , runTestNested $ Tx.goldenBudget "checkScriptContext2-20" $
          mkCheckScriptContext2Code (mkScriptContext 20)
    ]

testCheckScEquality :: TestTree
testCheckScEquality = testGroup "checkScriptContextEquality"
    [ runTestNested $ Tx.goldenBudget "checkScriptContexEqualityData-20" $
          mkScriptContextEqualityDataCode (mkScriptContext 20)
    , runTestNested $ Tx.goldenBudget "checkScriptContextEqualityTerm-20" $
          mkScriptContextEqualityTermCode (mkScriptContext 20)
    , runTestNested $ Tx.goldenBudget "checkScriptContextEqualityOverhead-20" $
          mkScriptContextEqualityOverheadCode (mkScriptContext 20)
    ]

allTests :: TestTree
allTests =
  testGroup "plutus-benchmark script-contexts tests"
    [ testCheckSc1
    , testCheckSc2
    , testCheckScEquality
    ]

main :: IO ()
main = defaultMain allTests
