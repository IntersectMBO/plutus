{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Contract
import qualified Spec.State
import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "plutus-contract" [
    Spec.Contract.tests,
    Spec.State.tests
    ]
