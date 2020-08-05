module Main where

import           Evaluation.ApplyBuiltinName (test_applyBuiltinName)

import           Test.Tasty

main :: IO ()
main = defaultMain $ testGroup "Untyped Plutus Core"
    [ test_applyBuiltinName
    ]
