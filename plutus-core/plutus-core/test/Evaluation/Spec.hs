module Evaluation.Spec where

import           Evaluation.ApplyBuiltinName (test_applyDefaultBuiltin)
import           Evaluation.DynamicBuiltins  (test_dynamicBuiltins)
import           Evaluation.Machines         (test_machines)

import           Test.Tasty

test_evaluation :: TestTree
test_evaluation =
    testGroup "evaluation"
        [ test_applyDefaultBuiltin
        , test_dynamicBuiltins
        , test_machines
        ]
