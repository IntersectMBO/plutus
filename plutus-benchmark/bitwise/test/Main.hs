module Main (main) where

import PlutusBenchmark.NQueens (nqueens)
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

main :: IO ()
main = defaultMain . testGroup "nqueens" $ [
  testCase "solves for 8 queens" $ assertEqual ""
    [(0,0), (1,4), (2,7), (3,5), (4,2), (5,6), (6,1), (7,3)]
    (nqueens 8)
  ]
