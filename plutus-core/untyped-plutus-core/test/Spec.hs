module Main where

import           Evaluation.Builtins (test_builtins)
import           Evaluation.Golden   (test_golden)
import           Evaluation.Machines
import           Transform.Simplify  (test_simplify)

import           Test.Tasty

main :: IO ()
main = defaultMain $ testGroup "Untyped Plutus Core"
    [ test_machines
    , test_builtins
    , test_memory
    , test_budget
    , test_golden
    , test_tallying
    , test_simplify
    ]
