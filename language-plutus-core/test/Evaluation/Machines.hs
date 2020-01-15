{-# LANGUAGE TypeApplications #-}

module Evaluation.Machines
    ( test_machines
    , test_memory
    , test_budget
    )
where

import           PlutusPrelude
import           PlcTestUtils
import           Common
import qualified Data.Text                     as T

import           Language.PlutusCore.FsTree     ( foldPlcFolderContents )
import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.L
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Generators.Test

import           Language.PlutusCore.Examples.Everything
                                                ( examples )
import           Language.PlutusCore.StdLib.Everything
                                                ( stdLib )

import           Control.Lens.Combinators       ( _1 )
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

testMachine
    :: Pretty err
    => String
    -> (  Term TyName Name ()
       -> Either (MachineException err) EvaluationResultDef
       )
    -> TestTree
testMachine machine eval' =
    testGroup machine $ fromInterestingTermGens $ \name ->
        testProperty name . propEvaluate eval'

test_machines :: TestTree
test_machines = testGroup
    "machines"
    [ testMachine "CK" $ pureTry @CkMachineException . evaluateCk
    , testMachine "CEK"
        $ (unwrapMachineException . view _1 . evaluateCek mempty Counting mempty
          )
    , testMachine "L" $ pureTry @LMachineException . evaluateL
    ]

testMemory :: ExMemoryUsage a => TestName -> a -> TestNested
testMemory name = nestedGoldenVsText name . T.pack . show . memoryUsage

test_memory :: TestTree
test_memory =
    runTestNestedIn ["test", "Evaluation", "Machines"]
        .  testNested "Memory"
        .  foldPlcFolderContents testNested testMemory testMemory
        $  stdLib
        <> examples

testBudget :: TestName -> (Plain Term) -> TestNested
testBudget name term =
    -- TODO use pretty here
                       nestedGoldenVsText
    name
    (T.pack $ show $ evaluateCek mempty Restricting (ExBudget 10 10) term)

test_budget :: TestTree
test_budget =
    runTestNestedIn ["test", "Evaluation", "Machines"]
        .  testNested "Budget"
        .  foldPlcFolderContents testNested
                                 (\name _ -> pure $ testCase name (pure ()))
                                 testBudget
        $  stdLib
        <> examples
