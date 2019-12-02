module Evaluation.Constant
    ( test_constant
    ) where

import           Evaluation.Constant.Success

import           Test.Tasty

-- TODO: why don't we have any tests for 'EvaluationFailure'?
test_constant :: TestTree
test_constant =
    testGroup "constant"
        [ test_constantSuccess
        ]
