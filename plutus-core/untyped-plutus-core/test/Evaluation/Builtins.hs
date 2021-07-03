module Evaluation.Builtins (test_builtins) where

import           Evaluation.Builtins.Definition (test_definition)
import           Evaluation.Builtins.MakeRead   (test_makeRead)

import           Test.Tasty

test_builtins :: TestTree
test_builtins =
    testGroup "builtins"
        [ test_definition
        , test_makeRead
        ]
