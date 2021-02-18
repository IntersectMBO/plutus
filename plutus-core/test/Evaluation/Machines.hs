{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}

module Evaluation.Machines
    ( test_machines
    )
where

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Generators.Test
import           Language.PlutusCore.Pretty

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
    [ testMachine "CK" $ evaluateCk defBuiltinsRuntime
    ]
