{- | Tests for the sorting and summation functions.  We're benchmarking PLC
   programs which are compiled from Haskell or are hand-written, so let's make
   sure that they do what they're supposed to. -}

module Main (main) where

import Test.Tasty

import Sort.Spec qualified as Sort
import Sum.Spec qualified as Sum

allTests :: TestTree
allTests =
  testGroup "plutus-benchmark list tests"
    [ Sort.tests
    , Sum.tests
    ]

main :: IO ()
main = defaultMain allTests
