module Main (main) where

import AsData.Spec qualified as AsData
import Inlineable.Spec qualified as Inlineable
import Match.Spec qualified as Match
import NoStrict.Spec qualified as NoStrict
import Strict.Spec qualified as Strict

import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Extras (runTestNested)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "frontend-plugin-tests"
    [ runTestNested
        ["test-frontend-plugin"]
        [ Strict.tests
        , NoStrict.tests
        , Inlineable.tests
        ]
    , AsData.tests
    , Match.tests
    ]
