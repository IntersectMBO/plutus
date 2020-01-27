module Evaluation.Spec where

import           Evaluation.ApplyBuiltinName (test_applyBuiltinName)
import           Evaluation.DynamicBuiltins  (test_dynamicBuiltins)
import           Evaluation.Golden           (test_golden)
import           Evaluation.Machines         (test_machines)

import           Test.Tasty

test_evaluation :: TestTree
test_evaluation =
    testGroup "evaluation"
        [ test_applyBuiltinName
        , test_dynamicBuiltins
        , test_golden
        , test_machines
        ]
