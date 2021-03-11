{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}

module Evaluation.Machines
    ( test_machines
    )
where

import           PlutusCore
import           PlutusCore.Evaluation.Machine.Ck
import           PlutusCore.Evaluation.Machine.ExMemory
import           PlutusCore.Evaluation.Machine.Exception
import           PlutusCore.Generators.Interesting
import           PlutusCore.Generators.Test
import           PlutusCore.Pretty

import           Test.Tasty
import           Test.Tasty.Hedgehog

testMachine
    :: (uni ~ DefaultUni, fun ~ DefaultFun, PrettyPlc internal)
    => String
    -> (Plain Term uni fun ->
           Either (EvaluationException user internal (Plain Term uni fun)) (Plain Term uni fun))
    -> TestTree
testMachine machine eval =
    testGroup machine $ fromInterestingTermGens $ \name ->
        testProperty name . propEvaluate eval

test_machines :: TestTree
test_machines = testGroup
    "machines"
    [ testMachine "CK" $ evaluateCkNoEmit defBuiltinsRuntime
    ]
