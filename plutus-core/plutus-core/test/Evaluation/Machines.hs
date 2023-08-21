-- editorconfig-checker-disable-file
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module Evaluation.Machines
    ( test_machines
    )
where

import GHC.Exts (fromString)
import PlutusCore
import PlutusCore.Evaluation.Machine.Ck
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Generators.Hedgehog.Interesting
import PlutusCore.Generators.Hedgehog.Test
import PlutusCore.Pretty

import Test.Tasty
import Test.Tasty.Hedgehog

testMachine
    :: (uni ~ DefaultUni, fun ~ DefaultFun, PrettyPlc internal)
    => String
    -> (Term TyName Name uni fun () ->
           Either (EvaluationException user internal (Term TyName Name uni fun ())) (Term TyName Name uni fun ()))
    -> TestTree
testMachine machine eval =
    testGroup machine $ fromInterestingTermGens $ \name ->
        testPropertyNamed name (fromString name) . propEvaluate eval

test_machines :: TestTree
test_machines = testGroup
    "machines"
    [ testMachine "CK" $ evaluateCkNoEmit defaultBuiltinsRuntime
    ]
