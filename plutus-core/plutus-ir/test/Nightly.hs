{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}

module Main (main) where

import NamesSpec

import Hedgehog
import Test.Tasty

main :: IO ()
main = defaultMain tests

numTestCases :: TestLimit
numTestCases = 100_000

tests :: TestTree
tests = testGroup "plutus-ir-nightly" [names numTestCases]
