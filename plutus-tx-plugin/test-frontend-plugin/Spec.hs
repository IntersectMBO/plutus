module Main (main) where

import Inlineable.Spec qualified as Inlineable
import NoStrict.Spec qualified as NoStrict
import Strict.Spec qualified as Strict

import Test.Tasty (TestTree, defaultMain)
import Test.Tasty.Extras (runTestNested)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  runTestNested
    ["test-frontend-plugin"]
    [ Strict.tests
    , NoStrict.tests
    , Inlineable.tests
    ]
