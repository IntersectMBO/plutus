{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Crowdfunding
import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "use cases" [
    Spec.Crowdfunding.tests
    ]
