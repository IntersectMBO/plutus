{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import LinearVesting.Test (validatorCodeFullyApplied)
import PlutusTx.Test (goldenBundle')
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Extras (TestNested, runTestNested, testNestedGhc)

main :: IO ()
main =
  defaultMain $ do
    testGroup
      "linear-vesting"
      [ runTestGhc [goldenBundle' "main" validatorCodeFullyApplied]
      ]

runTestGhc :: [TestNested] -> TestTree
runTestGhc = runTestNested ["linear-vesting", "test"] . pure . testNestedGhc
