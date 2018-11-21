module Main (main) where

import           CekMachine (test_evaluateCek)
import           Factorial  (test_dynamicFactorial)
import           String     (test_dynamicStrings)

import           Test.Tasty

test_Cek :: TestTree
test_Cek =
    testGroup "Cek"
        [ test_evaluateCek
        , test_dynamicFactorial
        , test_dynamicStrings
        ]

main :: IO ()
main = defaultMain test_Cek
