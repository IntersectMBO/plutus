{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Contract
import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "plutus-contract-test" [
    Spec.Contract.tests
    ]
