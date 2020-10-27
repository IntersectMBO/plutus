{- | Plutus benchmarks based on some nofib examples. -}

module Main where

import           Criterion.Main
import           Criterion.Types                                            (Config (..))
import qualified Data.Map                                                   as Map

import qualified Common

import           Language.PlutusCore                                        (Name (..))
import           Language.PlutusCore.Constant                               (DynamicBuiltinNameMeanings (..))
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Universe
import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek
import qualified Plutus.Benchmark.Clausify                                  as Clausify
import qualified Plutus.Benchmark.Knights                                   as Knights
import qualified Plutus.Benchmark.Prime                                     as Prime
import qualified Plutus.Benchmark.Queens                                    as Queens

emptyBuiltins :: DynamicBuiltinNameMeanings (CekValue DefaultUni)
emptyBuiltins =  DynamicBuiltinNameMeanings Map.empty


benchCek :: Term Name DefaultUni () -> Benchmarkable
benchCek program = nf (unsafeEvaluateCek getStringBuiltinMeanings defaultCostModel) program

benchClausify :: Clausify.StaticFormula -> Benchmarkable
benchClausify f = benchCek $ Clausify.mkClausifyTerm f

benchPrime :: Prime.PrimeID -> Benchmarkable
benchPrime pid = benchCek $ Prime.mkPrimalityBenchTerm pid

benchQueens :: Integer -> Queens.Algorithm -> Benchmarkable
benchQueens sz alg = benchCek $ Queens.mkQueensTerm sz alg

benchKnights :: Integer -> Integer -> Benchmarkable
benchKnights depth sz = benchCek $ Knights.mkKnightsTerm depth sz

config :: Config
config = defaultConfig {
           reportFile = Just "report.html"
         , template   = "./default.tpl"
         , timeLimit  = 60.0  -- Run each benchmark for at least one minute
         }

{- This runs all of the benchmarks, which will take a long time.
   To run an individual benmark, try, for example,

     stack bench plutus-benchmark -ba queens/bjbt

   Better results will be obtained with more repetitions of the benchmark.  Set
   the minimum time for the benchmarking process (in seconds) with the -L
   option. For example,

     stack bench plutus-benchmark -ba "queens/bjbt -L300"
-}

main :: IO ()
main = defaultMainWith config $ Common.mkBenchMarks benchClausify benchKnights benchPrime benchQueens
