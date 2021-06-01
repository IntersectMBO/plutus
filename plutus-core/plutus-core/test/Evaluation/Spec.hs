module Evaluation.Spec where

import           Evaluation.Machines (test_machines)

import           Test.Tasty

test_evaluation :: TestTree
test_evaluation =
    testGroup "evaluation"
        [ test_machines
        ]
