module Evaluation.Constant.All
    ( test_constant
    ) where

import           Evaluation.Constant.Failure
import           Evaluation.Constant.Resize
import           Evaluation.Constant.Success
import           Evaluation.Constant.SuccessFailure

import           Test.Tasty

test_constant :: TestTree
test_constant =
    testGroup "constant"
        [ test_constantSuccess
        , test_applyBuiltinNameSuccessFailure
        , test_constantFailure
        , test_resize
        ]
