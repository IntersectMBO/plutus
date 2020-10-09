{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}

module Evaluation.Machines
    ( test_machines
    , test_memory
    , test_budget
    , test_counting
    ) where

import           PlutusPrelude

import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek

import qualified Language.PlutusCore                                        as Plc
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.FsTree
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import           Language.PlutusCore.Examples.Everything                    (examples)
import           Language.PlutusCore.StdLib.Everything                      (stdLib)

import           Common
import           Data.String
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Text
import           Hedgehog                                                   hiding (Size, Var, eval)
import           Test.Tasty
import           Test.Tasty.Hedgehog

testMachine
    :: (uni ~ DefaultUni, Pretty internal, PrettyPlc termErr)
    => String
    -> (Term Name uni () -> Either (EvaluationException internal user termErr) (Term Name uni ()))
    -> TestTree
testMachine machine eval =
    testGroup machine $ fromInterestingTermGens $ \name genTermOfTbv ->
        testProperty name . withTests 200 . property $ do
            TermOf term val <- forAllWith mempty genTermOfTbv
            let resExp = erase <$> makeKnown @(Plc.Term TyName Name DefaultUni ()) val
            case extractEvaluationResult . eval $ erase term of
                Left err     -> fail $ show err
                Right resAct -> resAct === resExp

test_machines :: TestTree
test_machines =
    testGroup "machines"
        [ testMachine "CEK" $ evaluateCek mempty defaultCostModel
        ]

testMemory :: ExMemoryUsage a => TestName -> a -> TestNested
testMemory name = nestedGoldenVsText name . fromString . show . memoryUsage

test_memory :: TestTree
test_memory =
    runTestNestedIn ["untyped-plutus-core-test", "Evaluation", "Machines"]
        .  testNested "Memory"
        .  foldPlcFolderContents testNested testMemory testMemory
        $  stdLib
        <> examples

testBudget :: TestName -> Term Name DefaultUni () -> TestNested
testBudget name term =
                       nestedGoldenVsText
    name
    (renderStrict $ layoutPretty defaultLayoutOptions {layoutPageWidth = AvailablePerLine maxBound 1.0} $
        prettyPlcReadableDef $ runCek mempty (Restricting (ExRestrictingBudget (ExBudget 1000 1000))) defaultCostModel term)

bunchOfFibs :: PlcFolderContents DefaultUni
bunchOfFibs =
    let
        fibFile i = plcTermFile (show i) (naiveFib i)
    in
        FolderContents [ treeFolderContents "Fib" (fibFile <$> [1..3]) ]

test_budget :: TestTree
test_budget =
    runTestNestedIn ["untyped-plutus-core-test", "Evaluation", "Machines"]
        .  testNested "Budget"
        .  foldPlcFolderContents testNested
                                 (\name _ -> pure $ testGroup name [])
                                 (\name -> testBudget name . erase)
        $ examples <> bunchOfFibs

testCounting :: TestName -> Term Name DefaultUni () -> TestNested
testCounting name term =
                       nestedGoldenVsText
    name
    (renderStrict $ layoutPretty defaultLayoutOptions {layoutPageWidth = AvailablePerLine maxBound 1.0} $
        prettyPlcReadableDef $ runCekCounting mempty defaultCostModel term)

test_counting :: TestTree
test_counting =
    runTestNestedIn ["untyped-plutus-core-test", "Evaluation", "Machines"]
        .  testNested "Counting"
        .  foldPlcFolderContents testNested
                                 (\name _ -> pure $ testGroup name [])
                                 (\name -> testCounting name . erase)
        $ examples <> bunchOfFibs
