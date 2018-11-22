module DynamicBuiltins.Spec (test_dynamicBuiltins) where

import           DynamicBuiltins.Factorial (test_dynamicFactorial)
import           DynamicBuiltins.Logging   (test_logging)
import           DynamicBuiltins.String    (test_dynamicStrings)
import           Test.Tasty

test_dynamicBuiltins :: TestTree
test_dynamicBuiltins =
    testGroup "dynamicBuiltins"
        [ test_dynamicFactorial
        , test_dynamicStrings
        , test_logging
        ]
