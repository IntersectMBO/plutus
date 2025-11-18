module Main (main) where

import V1.Spec qualified as V1
import V2.Spec qualified as V2
import V3.Spec qualified as V3

import Test.Tasty

main :: IO ()
main =
  defaultMain
    ( testGroup
        "plutus-benchmark script-contexts tests"
        [V1.allTests, V2.allTests, V3.allTests]
    )
