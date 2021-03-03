module Evaluation.DynamicBuiltins (test_dynamicBuiltins) where

import           Evaluation.DynamicBuiltins.Definition (test_definition)
import           Evaluation.DynamicBuiltins.MakeRead   (test_dynamicMakeRead)

import           Test.Tasty

test_dynamicBuiltins :: TestTree
test_dynamicBuiltins =
    testGroup "dynamicBuiltins"
        [ test_definition
        , test_dynamicMakeRead
        ]
