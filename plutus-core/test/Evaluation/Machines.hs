{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}

module Evaluation.Machines
    ( test_machines
    , test_memory
    , test_budget
    , test_counting
    )
where

import           Common
import qualified Data.Text                                        as T
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Text

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.FsTree
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Generators.Test
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.Examples.Everything          (examples)
import           Language.PlutusCore.StdLib.Everything            (stdLib)

import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

testMachine
    :: (uni ~ DefaultUni, fun ~ DefaultFun, Pretty internal, PrettyPlc termErr)
    => String
    -> (Plain Term uni fun -> Either (EvaluationException internal user fun termErr) (Plain Term uni fun))
    -> TestTree
testMachine machine eval =
    testGroup machine $ fromInterestingTermGens $ \name ->
        testProperty name . propEvaluate eval

test_machines :: TestTree
test_machines = testGroup
    "machines"
    [ testMachine "CK"  $ evaluateCk  defBuiltinsRuntime
    , testMachine "CEK" $ evaluateCek defBuiltinsRuntime
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

testBudget :: TestName -> Plain Term DefaultUni DefaultFun -> TestNested
testBudget name term =
                       nestedGoldenVsText
    name
    (renderStrict $ layoutPretty defaultLayoutOptions {layoutPageWidth = AvailablePerLine maxBound 1.0} $
        prettyPlcReadableDef $ runCek defBuiltinsRuntime (Restricting (ExRestrictingBudget (ExBudget 1000 1000))) term)

bunchOfFibs :: PlcFolderContents DefaultUni DefaultFun
bunchOfFibs =
    let
        fibFile i = plcTermFile (show i) (naiveFib i)
    in
        FolderContents [ treeFolderContents "Fib" (fibFile <$> [1..3]) ]

test_budget :: TestTree
test_budget =
    runTestNestedIn ["test", "Evaluation", "Machines"]
        .  testNested "Budget"
        .  foldPlcFolderContents testNested
                                 (\name _ -> pure $ testCase name (pure ()))
                                 testBudget
        $ examples <> bunchOfFibs

testCounting :: TestName -> Plain Term DefaultUni DefaultFun -> TestNested
testCounting name term =
                       nestedGoldenVsText
    name
    (renderStrict $ layoutPretty defaultLayoutOptions {layoutPageWidth = AvailablePerLine maxBound 1.0} $
        prettyPlcReadableDef $ runCekCounting defBuiltinsRuntime term)

test_counting :: TestTree
test_counting =
    runTestNestedIn ["test", "Evaluation", "Machines"]
        .  testNested "Counting"
        .  foldPlcFolderContents testNested
                                 (\name _ -> pure $ testCase name (pure ()))
                                 testCounting
        $ examples <> bunchOfFibs
