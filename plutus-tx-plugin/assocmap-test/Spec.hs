module Main (main) where

import AssocMap.Spec qualified as AssocMap

import Test.Tasty (TestTree, defaultMain)
import Test.Tasty.Extras (embed, runTestNested)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  runTestNested
    ["assocmap-test"]
    [ AssocMap.goldenTests
    , embed AssocMap.propertyTests
    ]
