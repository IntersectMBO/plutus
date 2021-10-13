{- | Benchmarking for the Plutus versions of the Plutus nofib benchmarks. -}
{-# OPTIONS_GHC -fwarn-unused-imports #-}

module Main (main) where

import           Shared                         (mkBenchMarks)

import           Criterion.Main

import           PlutusBenchmark.Common         (getConfig)

import qualified PlutusBenchmark.NoFib.Clausify as Clausify
import qualified PlutusBenchmark.NoFib.Knights  as Knights
import qualified PlutusBenchmark.NoFib.Prime    as Prime
import qualified PlutusBenchmark.NoFib.Queens   as Queens

benchClausify :: Clausify.StaticFormula -> Benchmarkable
benchClausify f = nf Clausify.runClausify f

benchKnights :: Integer -> Integer -> Benchmarkable
benchKnights depth sz = nf (Knights.runKnights depth) sz

benchPrime :: Prime.PrimeID -> Benchmarkable
benchPrime pid = nf Prime.runFixedPrimalityTest pid

benchQueens :: Integer -> Queens.Algorithm -> Benchmarkable
benchQueens sz alg = nf (Queens.runQueens sz) alg

main :: IO ()
main = do
  let runners = (benchClausify, benchKnights, benchPrime, benchQueens)
  config <- getConfig 5.0  -- Run each benchmark for at least five seconds
  defaultMainWith config $ mkBenchMarks runners
