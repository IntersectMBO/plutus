module Main (main) where

import           CekMachine
import           DynamicBuiltins.Spec

import           Test.Tasty

test_Cek :: TestTree
test_Cek =
    testGroup "Cek"
        [ test_evaluateCek
        , test_dynamicBuiltins
        ]

main :: IO ()
main = defaultMain test_Cek
