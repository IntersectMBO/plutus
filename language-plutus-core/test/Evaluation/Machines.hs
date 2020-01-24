{-# LANGUAGE TypeApplications #-}

module Evaluation.Machines
    ( test_machines
    , test_memory
    , test_budget
    , test_counting
    )
where

import           Common
import qualified Data.Text                                        as T
import           PlcTestUtils
import           PlutusPrelude

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.L
import           Language.PlutusCore.FsTree                       
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Generators.Test
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.Examples.Everything          (examples)
import           Language.PlutusCore.StdLib.Everything            (stdLib)

import           Control.Lens.Combinators                         (_1)
import Data.Bitraversable
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit
import           Hedgehog                                 hiding (Size, Var)
import qualified Hedgehog.Gen                             as Gen
import qualified Hedgehog.Range                           as Range

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
                       nestedGoldenVsText
    name
    (docText $ prettyPlcReadableDef $ evaluateCek mempty Restricting (ExBudget 1000 1000) term)

bunchOfFibs :: PlcFolderContents
bunchOfFibs =
    let
        fibFile i = plcTermFile (show i) (naiveFib i)
    in
        FolderContents [ treeFolderContents "Fib" (fibFile <$> [1..10]) ]

test_budget :: TestTree
test_budget =
    runTestNestedIn ["test", "Evaluation", "Machines"]
        .  testNested "Budget"
        .  foldPlcFolderContents testNested
                                 (\name _ -> pure $ testCase name (pure ()))
                                 testBudget
        $ examples <> bunchOfFibs

testCounting :: TestName -> (Plain Term) -> TestNested
testCounting name term =
                       nestedGoldenVsText
    name
    (docText $ prettyPlcReadableDef $ evaluateCek mempty Counting mempty term)

test_counting :: TestTree
test_counting =
    runTestNestedIn ["test", "Evaluation", "Machines"]
        .  testNested "Counting"
        .  foldPlcFolderContents testNested
                                 (\name _ -> pure $ testCase name (pure ()))
                                 testCounting
        $ examples <> bunchOfFibs