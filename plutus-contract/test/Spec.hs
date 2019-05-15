{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Contract
import qualified Spec.Crowdfunding
import qualified Spec.Game
import qualified Spec.State
import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "plutus-contract" [
    Spec.Crowdfunding.tests,
    Spec.Contract.tests,
    Spec.Game.tests,
    Spec.State.tests
    ]
