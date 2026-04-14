module Main (main) where

import Array.Spec qualified as Array
import BuiltinList.Budget.Spec qualified as BuiltinList.Budget
import BuiltinList.NoCasing.Spec qualified as BuiltinList.NoCasing
import DataList.Budget.Spec qualified as DataList.Budget
import List.Spec qualified as List

import Test.Tasty (TestTree, defaultMain)
import Test.Tasty.Extras (embed, runTestNested)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  runTestNested
    ["list-test"]
    [ Array.smokeTests
    , BuiltinList.Budget.tests
    , BuiltinList.NoCasing.tests
    , DataList.Budget.tests
    , embed List.propertyTests
    ]
