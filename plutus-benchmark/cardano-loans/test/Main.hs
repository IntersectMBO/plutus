{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import CardanoLoans.Test (validatorCodeFullyApplied)
import PlutusTx.Test (goldenBundle')
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Extras (TestNested, runTestNested, testNestedGhc)

main :: IO ()
main =
  defaultMain $ do
    testGroup
      "cardano-loans"
      [ runTestGhc [goldenBundle' "main" validatorCodeFullyApplied]
      ]

runTestGhc :: [TestNested] -> TestTree
runTestGhc = runTestNested ["cardano-loans", "test"] . pure . testNestedGhc
