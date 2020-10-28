{- | Plutus benchmarks based on some nofib examples. -}

module Main where

import           Criterion.Main

import           Common

import           Language.PlutusCore                               (Name (..))
import           Language.PlutusCore.Builtins
import           Language.PlutusCore.Universe
import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek
import qualified Plutus.Benchmark.Clausify                         as Clausify
import qualified Plutus.Benchmark.Knights                          as Knights
import qualified Plutus.Benchmark.Prime                            as Prime
import qualified Plutus.Benchmark.Queens                           as Queens


benchCek :: Term Name DefaultUni DefaultFun () -> Benchmarkable
benchCek program = nf (unsafeEvaluateCek defBuiltinsRuntime) program

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

     stack bench plutus-benchmark -ba queens/bjbt

   Better results will be obtained with more repetitions of the benchmark.  Set
   the minimum time for the benchmarking process (in seconds) with the -L
   option. For example,

     stack bench plutus-benchmark -ba "queens/bjbt -L300"
-}

main :: IO ()
main = do
  let runners = (benchClausify, benchKnights, benchPrime, benchQueens)
  config <- Common.getConfig 60.0  -- Run each benchmark for at least one minute
  defaultMainWith config $ Common.mkBenchMarks runners
