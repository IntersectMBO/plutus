module Main (main) where

import V1.Spec qualified as V1
import V3.Spec qualified as V3

import Test.Tasty

main :: IO ()
main = defaultMain (testGroup "plutus-benchmark script-contexts tests" [V1.allTests, V3.allTests])
