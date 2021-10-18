{- | Tests for the Plutus nofib benchmarks, mostly comparing the result of Plutus
evaluation with the result of Haskell evaluation. Lastpiece is currently omitted
because its memory consumption as a Plutus program is too great to allow it to
run to completion. -}

module Main (main) where

import           Test.Tasty

import qualified Sort.Spec  as Sort
import qualified Sum.Spec   as Sum

allTests :: TestTree
allTests =
  testGroup "plutus-benchmark list tests"
    [ Sort.tests
    , Sum.tests
    ]

main :: IO ()
main = defaultMain allTests
