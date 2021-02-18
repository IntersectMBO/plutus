module Main where

import           Evaluation.ApplyBuiltinName (test_applyStaticBuiltin)
import           Evaluation.Golden           (test_golden)
import           Evaluation.Machines

import           Test.Tasty

main :: IO ()
main = defaultMain $ testGroup "Untyped Plutus Core"
    [ test_applyStaticBuiltin
    , test_machines
    , test_memory
    , test_budget
    , test_golden
    , test_counting
    ]
