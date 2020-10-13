module Evaluation.Spec where

import           Evaluation.ApplyBuiltinName (test_applyStaticBuiltin)
import           Evaluation.DynamicBuiltins  (test_dynamicBuiltins)
import           Evaluation.Golden           (test_golden)
import           Evaluation.Machines         (test_budget, test_counting, test_machines, test_memory)

import           Test.Tasty

test_evaluation :: TestTree
test_evaluation =
    testGroup "evaluation"
        [ test_applyStaticBuiltin
        , test_dynamicBuiltins
        , test_golden
        , test_machines
        , test_memory
        , test_budget
        , test_counting
        ]
