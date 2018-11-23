module Main (main) where

import           CekMachine           (test_evaluateCek)
import           DynamicBuiltins.Spec (test_dynamicBuiltins)
import           LMachine             (test_evaluateL)

import           Test.Tasty

test_Cek_and_L :: TestTree
test_Cek_and_L =
    testGroup "Cek_and_L"
        [ test_evaluateCek
        , test_evaluateL
        , test_dynamicBuiltins
        ]

main :: IO ()
main = defaultMain test_Cek_and_L
