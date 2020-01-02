{-# LANGUAGE TypeApplications #-}

module Evaluation.Machines
    ( test_machines
    ) where

import           PlcTestUtils

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.L
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Generators.Test
import           Language.PlutusCore.Pretty
import Data.Tuple.Select

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
