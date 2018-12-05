module Main (main) where

import           CekMachine           (test_evaluateCek)
import           DynamicBuiltins.Spec (test_dynamicBuiltins)
import           LMachine             (test_evaluateL)

import           Test.Tasty

test_machines :: TestTree
test_machines =
    testGroup "test_machines"
        [ test_evaluateCek
        , test_evaluateL
        , test_dynamicBuiltins
        ]

main :: IO ()
main = defaultMain test_machines
