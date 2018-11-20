module Main (main) where

import           CekMachine

import           Test.Tasty

test_Cek :: TestTree
test_Cek =
    testGroup "Cek"
        [ test_evaluateCek
        ]

main :: IO ()
main = defaultMain test_Cek
