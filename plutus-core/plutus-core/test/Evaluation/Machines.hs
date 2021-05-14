{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}

module Evaluation.Machines
    ( test_machines
    )
where

import           PlutusCore
import           PlutusCore.Evaluation.Machine.Ck
import           PlutusCore.Evaluation.Machine.Exception
import           PlutusCore.Generators.Interesting
import           PlutusCore.Generators.Test
import           PlutusCore.Pretty


import           Test.Tasty
import           Test.Tasty.Hedgehog

testMachine
    :: (uni ~ DefaultUni, fun ~ DefaultFun, PrettyPlc internal)
    => String
    -> (Term TyName Name uni fun () ->
           Either (EvaluationException user internal (Term TyName Name uni fun ())) (Term TyName Name uni fun ()))
    -> TestTree
testMachine machine eval =
    testGroup machine $ fromInterestingTermGens $ \name ->
        testProperty name . propEvaluate eval

test_machines :: TestTree
test_machines = testGroup
    "machines"
    [ testMachine "CK" $ evaluateCkNoEmit defaultBuiltinsRuntime
    ]
