module Main where

import Spec.Budget qualified
import Spec.Data.Budget qualified
import Spec.Data.Value qualified
import Spec.ReturnUnit.V1 qualified
import Spec.ReturnUnit.V2 qualified
import Spec.ReturnUnit.V3 qualified
import Spec.ScriptSize qualified
import Spec.Value qualified

import Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "plutus-ledger-api-plugin-test"
    [ Spec.Budget.tests
    , Spec.Data.Budget.tests
    , Spec.Data.Value.test_EqValue
    , Spec.ReturnUnit.V1.tests
    , Spec.ReturnUnit.V2.tests
    , Spec.ReturnUnit.V3.tests
    , Spec.ScriptSize.tests
    , Spec.Value.test_EqValue
    ]
