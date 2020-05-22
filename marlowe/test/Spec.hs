{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Marlowe.Marlowe

import           Test.Tasty
import           Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain tests


tests :: TestTree
tests = testGroup "Marlowe"
    [ testGroup "Contracts" [ Spec.Marlowe.Marlowe.tests]
    , testGroup "Static Analysis"
        [ testProperty "No false positives" Spec.Marlowe.Marlowe.prop_noFalsePositives ]
    ]
