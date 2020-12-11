{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Marlowe.Actus

import           Test.Tasty

main :: IO ()
main = defaultMain tests


tests :: TestTree
tests = testGroup "Marlowe Contracts"
        [
                Spec.Marlowe.Actus.tests
        ]


