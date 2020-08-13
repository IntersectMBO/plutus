module Main where

import           Evaluation.ApplyBuiltinName (test_applyStaticBuiltinName)

import           Test.Tasty

main :: IO ()
main = defaultMain $ testGroup "Untyped Plutus Core"
    [ test_applyStaticBuiltinName
    ]
