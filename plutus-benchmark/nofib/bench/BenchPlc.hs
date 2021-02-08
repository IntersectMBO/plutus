{-# LANGUAGE TypeApplications #-}

{- | Plutus benchmarks based on some nofib examples. -}
module Main where

import           Criterion.Main

import           Common

import           Control.Exception
import           Control.Monad.Except
import qualified Language.PlutusCore                               as PLC
import           Language.PlutusCore.Builtins
import           Language.PlutusCore.Universe
import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek
import qualified Plutus.Benchmark.Clausify                         as Clausify
import qualified Plutus.Benchmark.Knights                          as Knights
import qualified Plutus.Benchmark.Prime                            as Prime
import qualified Plutus.Benchmark.Queens                           as Queens


benchCek :: Term NamedDeBruijn DefaultUni DefaultFun () -> Benchmarkable
benchCek t = case runExcept @PLC.FreeVariableError $ PLC.runQuoteT $ unDeBruijnTerm t of
    Left e   -> throw e
    Right t' -> nf (unsafeEvaluateCek defBuiltinsRuntime) t'

benchClausify :: Clausify.StaticFormula -> Benchmarkable
benchClausify f = benchCek $ Clausify.mkClausifyTerm f

benchPrime :: Prime.PrimeID -> Benchmarkable
benchPrime pid = benchCek $ Prime.mkPrimalityBenchTerm pid

benchQueens :: Integer -> Queens.Algorithm -> Benchmarkable
benchQueens sz alg = benchCek $ Queens.mkQueensTerm sz alg

benchKnights :: Integer -> Integer -> Benchmarkable
benchKnights depth sz = benchCek $ Knights.mkKnightsTerm depth sz

{- This runs all of the benchmarks, which will take a long time.
   To run an individual benmark, try, for example,

     stack bench plutus-benchmark:nofib --ba primetest/40digits

   or

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

main :: IO ()
main = do
  let runners = (benchClausify, benchKnights, benchPrime, benchQueens)
  config <- Common.getConfig 60.0  -- Run each benchmark for at least one minute
  defaultMainWith config $ Common.mkBenchMarks runners
