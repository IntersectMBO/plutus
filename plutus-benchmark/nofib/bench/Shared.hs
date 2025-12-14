-- | Shared code for benchmarking Plutus and Haskell versions of the Plutus nofib examples
module Shared
  ( benchWith
  , mkBenchMarks
  , benchTermCek
  ) where

import PlutusBenchmark.Common (Term, benchTermCek, getConfig)

import PlutusBenchmark.NoFib.Clausify qualified as Clausify
import PlutusBenchmark.NoFib.Knights qualified as Knights
import PlutusBenchmark.NoFib.Prime qualified as Prime
import PlutusBenchmark.NoFib.Queens qualified as Queens

import Criterion.Main

-- | Package together functions to create benchmarks for each program given suitable inputs.
type BenchmarkRunners =
  ( Clausify.StaticFormula -> Benchmarkable
  , Integer -> Integer -> Benchmarkable
  , Prime.PrimeID -> Benchmarkable
  , Integer -> Queens.Algorithm -> Benchmarkable
  )

{-| Make a benchmarks with a number of different inputs.  The input values have
   been chosen to complete in a reasonable time. -}
mkBenchMarks :: BenchmarkRunners -> [Benchmark]
mkBenchMarks (benchClausify, benchKnights, benchPrime, benchQueens) =
  [ bgroup
      "clausify"
      [ bench "formula1" $ benchClausify Clausify.F1
      , bench "formula2" $ benchClausify Clausify.F2
      , bench "formula3" $ benchClausify Clausify.F3
      , bench "formula4" $ benchClausify Clausify.F4
      , bench "formula5" $ benchClausify Clausify.F5
      ]
  , bgroup
      "knights"
      [ bench "4x4" $ benchKnights 100 4
      , bench "6x6" $ benchKnights 100 6
      , bench "8x8" $ benchKnights 100 8
      ]
  , bgroup
      "primetest"
      [ bench "05digits" $ benchPrime Prime.P5
      , bench "10digits" $ benchPrime Prime.P10
      , bench "30digits" $ benchPrime Prime.P30
      , bench "50digits" $ benchPrime Prime.P50
      -- Larger primes are available in Primes.hs, but may take a long time.
      ]
  , bgroup
      "queens4x4"
      [ -- N-queens problem on a 4x4 board
        bench "bt" $ benchQueens 4 Queens.Bt
      , bench "bm" $ benchQueens 4 Queens.Bm
      , bench "bjbt1" $ benchQueens 4 Queens.Bjbt1
      , bench "bjbt2" $ benchQueens 4 Queens.Bjbt2
      , bench "fc" $ benchQueens 4 Queens.Fc
      ]
  , bgroup
      "queens5x5"
      [ -- N-queens problem on a 5x5 board
        bench "bt" $ benchQueens 5 Queens.Bt
      , bench "bm" $ benchQueens 5 Queens.Bm
      , bench "bjbt1" $ benchQueens 5 Queens.Bjbt1
      , bench "bjbt2" $ benchQueens 5 Queens.Bjbt2
      , bench "fc" $ benchQueens 5 Queens.Fc
      ]
  ]

---------------- Create a benchmark with given inputs ----------------

benchClausifyWith :: (Term -> Benchmarkable) -> Clausify.StaticFormula -> Benchmarkable
benchClausifyWith benchmarker f = benchmarker $ Clausify.mkClausifyTerm f

benchPrimeWith :: (Term -> Benchmarkable) -> Prime.PrimeID -> Benchmarkable
benchPrimeWith benchmarker pid = benchmarker $ Prime.mkPrimalityBenchTerm pid

benchQueensWith :: (Term -> Benchmarkable) -> Integer -> Queens.Algorithm -> Benchmarkable
benchQueensWith benchmarker sz alg = benchmarker $ Queens.mkQueensTerm sz alg

benchKnightsWith :: (Term -> Benchmarkable) -> Integer -> Integer -> Benchmarkable
benchKnightsWith benchmarker depth sz = benchmarker $ Knights.mkKnightsTerm depth sz

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
benchWith :: (Term -> Benchmarkable) -> IO ()
benchWith benchmarker = do
  let runners =
        ( benchClausifyWith benchmarker
        , benchKnightsWith benchmarker
        , benchPrimeWith benchmarker
        , benchQueensWith benchmarker
        )
  -- Run each benchmark for at least one minute.  Change this with -L or --timeout.
  config <- getConfig 60.0
  defaultMainWith config $ mkBenchMarks runners
