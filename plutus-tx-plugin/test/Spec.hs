module Main (main) where

import AsData.Budget.Spec qualified as AsData.Budget

import Test.Tasty (TestTree, defaultMain)
import Test.Tasty.Extras (embed, runTestNested)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  runTestNested
    ["test"]
    [ AsData.Budget.tests
    ]
