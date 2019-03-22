module DynamicBuiltins.Spec (test_dynamicBuiltins) where

import           DynamicBuiltins.Definition (test_definition)
import           DynamicBuiltins.Logging    (test_logging)
import           DynamicBuiltins.MakeRead   (test_dynamicMakeRead)
import           Test.Tasty

test_dynamicBuiltins :: TestTree
test_dynamicBuiltins =
    testGroup "dynamicBuiltins"
        [ test_definition
        , test_dynamicMakeRead
        , test_logging
        ]
