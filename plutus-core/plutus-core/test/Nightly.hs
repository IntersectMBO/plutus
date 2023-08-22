{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}

module Main (main) where

import Names.Spec

import Hedgehog
import Test.Tasty

main :: IO ()
main = defaultMain tests

numTestCases :: TestLimit
numTestCases = 100_000

tests :: TestTree
tests = testGroup "plutus-core-nightly" [test_names numTestCases]
