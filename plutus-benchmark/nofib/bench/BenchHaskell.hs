{- | Benchmarking for the Plutus versions of the Plutus nofib benchmarks. -}
{-# OPTIONS_GHC -fwarn-unused-imports #-}

module Main (main) where

import qualified Common

import           Criterion.Main
import           Criterion.Types           (Config (..))

import qualified Plutus.Benchmark.Clausify as Clausify
import qualified Plutus.Benchmark.Knights  as Knights
import qualified Plutus.Benchmark.Prime    as Prime
import qualified Plutus.Benchmark.Queens   as Queens

benchClausify :: Clausify.StaticFormula -> Benchmarkable
benchClausify f = nf Clausify.mkClausifyTerm f

benchKnights :: Integer -> Integer -> Benchmarkable
benchKnights depth sz =nf (Knights.mkKnightsTerm depth) sz

benchPrime :: Prime.PrimeID -> Benchmarkable
benchPrime pid = nf Prime.mkPrimalityBenchTerm pid

benchQueens :: Integer -> Queens.Algorithm -> Benchmarkable
benchQueens sz alg = nf (Queens.mkQueensTerm sz) alg

config :: Config
config = defaultConfig {
           reportFile = Just "report.html"
         , template   = "./default.tpl"
         , timeLimit  = 5.0  -- Run each benchmark for at least five seconds
         }

main :: IO ()
main = defaultMainWith config $ Common.mkBenchMarks benchClausify benchKnights benchPrime benchQueens
