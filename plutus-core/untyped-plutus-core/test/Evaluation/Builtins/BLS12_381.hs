module Evaluation.Builtins.BLS12_381 (test_BLS12_381)
where

import Evaluation.Builtins.BLS12_381.HaskellTests as HaskellTests
import Evaluation.Builtins.BLS12_381.PlutusTests as PlutusTests

import Test.Tasty

test_BLS12_381 :: TestTree
test_BLS12_381 =
    testGroup "BLS12-381"
    [ HaskellTests.tests
    , PlutusTests.tests
    ]
