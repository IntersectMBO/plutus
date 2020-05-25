{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Marlowe.Marlowe
import           System.Exit
import qualified Spec.Marlowe.Marlowe2
import           Test.Tasty
import           Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain tests


tests :: TestTree
tests = testGroup "Marlowe"
    [ testGroup "Contracts" [ {- Spec.Marlowe.Marlowe.tests, -} Spec.Marlowe.Marlowe2.tests]
    , testGroup "Static Analysis"
        [ {- testProperty "No false positives" Spec.Marlowe.Marlowe.prop_noFalsePositives -} ]
    ]
