module Evaluation.Constant.All
    ( test_constantApplication
    ) where

import           Evaluation.Constant.Failure
import           Evaluation.Constant.Resize
import           Evaluation.Constant.Success
import           Evaluation.Constant.SuccessFailure

import           Test.Tasty

test_constantApplication :: TestTree
test_constantApplication =
    testGroup "constantApplication"
        [ test_applyBuiltinNameSuccess
        , test_applyBuiltinNameSuccessFailure
        , test_applyBuiltinNameFailure
        , test_resize
        ]
