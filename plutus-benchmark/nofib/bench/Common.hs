{- | Shared code for benchmarking Plutus and Haskell versions of the Plutus nofib examples -}
module Common
where

import           Criterion.Main

import qualified Plutus.Benchmark.Clausify as Clausify
import qualified Plutus.Benchmark.Prime    as Prime
import qualified Plutus.Benchmark.Queens   as Queens

mkBenchMarks
    :: (Clausify.StaticFormula -> Benchmarkable)
    -> (Integer -> Integer -> Benchmarkable)
    -> (Prime.PrimeID -> Benchmarkable)
    -> (Integer -> Queens.Algorithm -> Benchmarkable)
    -> [Benchmark]
mkBenchMarks benchClausify benchKnights benchPrime benchQueens = [
    bgroup "clausify" [ bench "formula1" $ benchClausify Clausify.F1
                      , bench "formula2" $ benchClausify Clausify.F2
                      , bench "formula3" $ benchClausify Clausify.F3
                      , bench "formula4" $ benchClausify Clausify.F4
                      , bench "formula5" $ benchClausify Clausify.F5
                      ]
  , bgroup "knights" [ bench "4x4" $ benchKnights 100 4
                     , bench "6x6" $ benchKnights 100 6
                     , bench "8x8" $ benchKnights 100 8
                     ]
  , bgroup "primetest" [ bench "05digits" $ benchPrime Prime.P5
                       , bench "08digits" $ benchPrime Prime.P8
                       , bench "10digits" $ benchPrime Prime.P10
                       , bench "20digits" $ benchPrime Prime.P20
                       , bench "30digits" $ benchPrime Prime.P30
                       , bench "40digits" $ benchPrime Prime.P40
                       ]
  , bgroup "queens4x4" [ -- N-queens problem on a 4x4 board
                      bench "bt"    $ benchQueens 4 Queens.Bt
                    , bench "bm"    $ benchQueens 4 Queens.Bm
                    , bench "bjbt1" $ benchQueens 4 Queens.Bjbt1
                    , bench "bjbt2" $ benchQueens 4 Queens.Bjbt2
                    , bench "fc"    $ benchQueens 4 Queens.Fc
                    ]
  , bgroup "queens5x5" [ -- N-queens problem on a 5x5 board
                      bench "bt"    $ benchQueens 5 Queens.Bt
                    , bench "bm"    $ benchQueens 5 Queens.Bm
                    , bench "bjbt1" $ benchQueens 5 Queens.Bjbt1
                    , bench "bjbt2" $ benchQueens 5 Queens.Bjbt2
                    , bench "fc"    $ benchQueens 5 Queens.Fc
                    ]
       ]

