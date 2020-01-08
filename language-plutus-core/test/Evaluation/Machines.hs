{-# LANGUAGE TypeApplications #-}

module Evaluation.Machines
    ( test_machines
    , test_memory
    ) where

import           PlcTestUtils
import Common
import qualified Data.Text as T

import           Language.PlutusCore.FsTree              (foldPlcFolderContents)
import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.L
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Generators.Test
import           Language.PlutusCore.Pretty
import Data.Tuple.Select

import           Language.PlutusCore.Examples.Everything (examples)
import           Language.PlutusCore.StdLib.Everything   (stdLib)

import           Test.Tasty
import           Test.Tasty.Hedgehog

testMachine
    :: Pretty err
    => String
    -> (Term TyName Name () -> Either (MachineException err) EvaluationResultDef)
    -> TestTree
testMachine machine eval =
    testGroup machine $ fromInterestingTermGens $ \name ->
        testProperty name . propEvaluate eval

test_machines :: TestTree
test_machines = testGroup "machines"
    [ testMachine "CK"  $ pureTry @CkMachineException . evaluateCk
    , testMachine "CEK" $ (sel1 . evaluateCek @() @() mempty ())
    , testMachine "L"   $ pureTry @LMachineException . evaluateL
    ]

testMemory :: ExMemoryUsage a => TestName -> a -> TestNested
testMemory name = nestedGoldenVsText name . T.pack . show . memoryUsage

test_memory :: TestTree
test_memory
    = runTestNestedIn ["test", "Evaluation", "Machines"]
    . testNested "Memory"
    . foldPlcFolderContents testNested testMemory testMemory
    $ stdLib <> examples