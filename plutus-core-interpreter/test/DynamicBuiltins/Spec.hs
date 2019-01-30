module DynamicBuiltins.Spec (test_dynamicBuiltins) where

import           DynamicBuiltins.Factorial (test_dynamicFactorial)
import           DynamicBuiltins.Logging   (test_logging)
import           DynamicBuiltins.MakeRead  (test_dynamicMakeRead)
import           Test.Tasty

test_dynamicBuiltins :: TestTree
test_dynamicBuiltins =
    testGroup "dynamicBuiltins"
        [ test_dynamicFactorial
        , test_dynamicMakeRead
        , test_logging
        ]
