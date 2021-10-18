{- | Tests for the sorting and summation functions.  We're benchmarking PLC
   programs which are compiled from Haskell or are hand-written, so let's make
   sure that they do what they're supposed to. -}

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
