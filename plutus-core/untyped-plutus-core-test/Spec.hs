module Main where

import           Evaluation.ApplyBuiltinName (test_applyStaticBuiltinName)
import           Evaluation.Machines

import           Test.Tasty

main :: IO ()
main = defaultMain $ testGroup "Untyped Plutus Core"
    [ test_applyStaticBuiltinName
    , test_machines
    , test_memory
    , test_budget
    , test_counting
    ]
