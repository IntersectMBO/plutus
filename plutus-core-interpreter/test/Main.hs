module Main (main) where

import           CekMachine           (test_evaluateCek)
import           DynamicBuiltins.Spec (test_dynamicBuiltins)

import           Test.Tasty

test_Cek :: TestTree
test_Cek =
    testGroup "Cek"
        [ test_evaluateCek
        , test_dynamicBuiltins
        ]

main :: IO ()
main = defaultMain test_Cek
