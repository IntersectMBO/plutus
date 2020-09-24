module Evaluation.DynamicBuiltins (test_dynamicBuiltins) where

import           Evaluation.Builtins.Definition (test_definition)
import           Evaluation.Builtins.MakeRead   (test_dynamicMakeRead)

import           Test.Tasty

test_dynamicBuiltins :: TestTree
test_dynamicBuiltins =
    testGroup "dynamicBuiltins"
        [ test_definition
        , test_dynamicMakeRead
        ]
