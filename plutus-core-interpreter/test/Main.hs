module Main where

import           CekMachine

import           Test.Tasty

main :: IO ()
main = defaultMain test_evaluateCek
