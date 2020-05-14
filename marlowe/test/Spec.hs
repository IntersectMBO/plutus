{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

-- import qualified Spec.Actus
import qualified Spec.Marlowe.Marlowe
import           System.Exit
import qualified Tests

import           Test.Tasty

main :: IO ()
main = do
    good <- and <$> sequence [Tests.runTests]
    if good
    then defaultMain tests
    else exitFailure


tests :: TestTree
tests = testGroup "Marlowe Contracts"
        [ Spec.Marlowe.Marlowe.tests
        ]
