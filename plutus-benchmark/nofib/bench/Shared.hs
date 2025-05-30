{- | Shared code for benchmarking Plutus and Haskell versions of the Plutus nofib examples -}
module Shared (
    benchWith
    , mkBenchMarks
    , benchTermCek
    ) where

import PlutusBenchmark.Common (Term, benchTermCek, getConfig)

import PlutusBenchmark.NoFib.Clausify qualified as Clausify
import PlutusBenchmark.NoFib.Knights qualified as Knights
import PlutusBenchmark.NoFib.Prime qualified as Prime
import PlutusBenchmark.NoFib.Queens qualified as Queens

import Criterion.Main


{- | Package together functions to create benchmarks for each program given suitable inputs. -}
type BenchmarkRunners =
    ( String -> Clausify.StaticFormula -> Benchmark
    , String -> Integer -> Integer -> Benchmark
    , String -> Prime.PrimeID -> Benchmark
    , String -> Integer -> Queens.Algorithm -> Benchmark
    )

{- | Make a benchmarks with a number of different inputs.  The input values have
   been chosen to complete in a reasonable time. -}
mkBenchMarks :: BenchmarkRunners -> [Benchmark]
mkBenchMarks (benchClausify, benchKnights, benchPrime, benchQueens) = [
    bgroup "clausify" [ benchClausify "formula1" Clausify.F1
                      , benchClausify "formula2" Clausify.F2
                      , benchClausify "formula3" Clausify.F3
                      , benchClausify "formula4" Clausify.F4
                      , benchClausify "formula5" Clausify.F5
                      ]
  , bgroup "knights" [ benchKnights "4x4" 100 4
                     , benchKnights "6x6" 100 6
                     , benchKnights "8x8" 100 8
                     ]
  , bgroup "primetest" [ benchPrime "05digits" Prime.P5
                       , benchPrime "10digits" Prime.P10
                       , benchPrime "30digits" Prime.P30
                       , benchPrime "50digits" Prime.P50
                       -- Larger primes are available in Primes.hs, but may take a long time.
                       ]
  , bgroup "queens4x4" [ -- N-queens problem on a 4x4 board
                      benchQueens "bt"    4 Queens.Bt
                    , benchQueens "bm"    4 Queens.Bm
                    , benchQueens "bjbt1" 4 Queens.Bjbt1
                    , benchQueens "bjbt2" 4 Queens.Bjbt2
                    , benchQueens "fc"    4 Queens.Fc
                    ]
  , bgroup "queens5x5" [ -- N-queens problem on a 5x5 board
                      benchQueens "bt"    5 Queens.Bt
                    , benchQueens "bm"    5 Queens.Bm
                    , benchQueens "bjbt1" 5 Queens.Bjbt1
                    , benchQueens "bjbt2" 5 Queens.Bjbt2
                    , benchQueens "fc"    5 Queens.Fc
                    ]
       ]


---------------- Create a benchmark with given inputs ----------------

benchClausifyWith
    :: (String -> Term -> Benchmark) -> String -> Clausify.StaticFormula -> Benchmark
benchClausifyWith benchmarker name f = benchmarker name $ Clausify.mkClausifyTerm f

benchPrimeWith :: (String -> Term -> Benchmark) -> String -> Prime.PrimeID -> Benchmark
benchPrimeWith benchmarker name pid = benchmarker name $ Prime.mkPrimalityBenchTerm pid

benchQueensWith
    :: (String -> Term -> Benchmark) -> String -> Integer -> Queens.Algorithm -> Benchmark
benchQueensWith benchmarker name sz alg = benchmarker name $ Queens.mkQueensTerm sz alg

benchKnightsWith
    :: (String -> Term -> Benchmark) -> String -> Integer -> Integer -> Benchmark
benchKnightsWith benchmarker name depth sz = benchmarker name $ Knights.mkKnightsTerm depth sz

{- This runs all of the benchmarks, which will take a long time.
   To run an individual benmark, try, for example,

     cabal bench plutus-benchmark:nofib --benchmark-options "primetest/40digits".

   Better results will be obtained with more repetitions of the benchmark.  Set
   the minimum time for the benchmarking process (in seconds) with the -L
   option. For example,

     stack bench plutus-benchmark:nofib --ba "primetest/40digits -L300"

   You can list the avaiable benchmarks with

     stack bench plutus-benchmark:nofib --ba --list

   or

     cabal bench plutus-benchmark:nofib --benchmark-options --list

-}


-- Given a function (involving some evaluator) which constructs a Benchmarkable
-- from a Term, use it to construct and run all of the benchmarks
benchWith :: (String -> Term -> Benchmark) -> IO ()
benchWith benchmarker = do
  let runners = ( benchClausifyWith benchmarker, benchKnightsWith benchmarker
                , benchPrimeWith benchmarker, benchQueensWith benchmarker)
  -- Run each benchmark for at least one minute.  Change this with -L or --timeout.
  config <- getConfig 60.0
  defaultMainWith config $ mkBenchMarks runners
