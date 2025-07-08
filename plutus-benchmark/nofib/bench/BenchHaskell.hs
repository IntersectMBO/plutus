{- | Benchmarking for the Haskell versions of the Plutus nofib benchmarks. -}
module Main (main) where

import Shared (mkBenchMarks)

import Criterion.Main

import PlutusBenchmark.Common (getConfig)

import PlutusBenchmark.NoFib.Clausify qualified as Clausify
import PlutusBenchmark.NoFib.Knights qualified as Knights
import PlutusBenchmark.NoFib.Prime qualified as Prime
import PlutusBenchmark.NoFib.Queens qualified as Queens

benchClausify :: String -> Clausify.StaticFormula -> Benchmark
benchClausify name f = bench name $ whnf Clausify.runClausify f

benchKnights :: String -> Integer -> Integer -> Benchmark
benchKnights name depth sz = bench name $ whnf (Knights.runKnights depth) sz

benchPrime :: String -> Prime.PrimeID -> Benchmark
benchPrime name pid = bench name $ whnf Prime.runFixedPrimalityTest pid

benchQueens :: String -> Integer -> Queens.Algorithm -> Benchmark
benchQueens name sz alg = bench name $ whnf (Queens.runQueens sz) alg

main :: IO ()
main = do
  let runners = (benchClausify, benchKnights, benchPrime, benchQueens)
  config <- getConfig 5.0  -- Run each benchmark for at least five seconds
  defaultMainWith config $ mkBenchMarks runners
