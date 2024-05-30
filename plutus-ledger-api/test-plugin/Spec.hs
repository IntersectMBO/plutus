module Main where

import Spec.Budget qualified
import Spec.Data.Budget qualified
import Spec.Data.Value qualified
import Spec.Value qualified

import Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "plutus-ledger-api-plugin-test"
    [ Spec.Budget.tests
    , Spec.Value.test_EqValue
    , Spec.Data.Budget.tests
    , Spec.Data.Value.test_EqValue
    ]
