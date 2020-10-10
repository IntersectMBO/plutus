module Main where

import           Criterion.Main
import           Criterion.Types                                            (Config (..))
import qualified Data.Map                                                   as Map

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
benchCek program =
  nf (unsafeEvaluateCek getStringBuiltinMeanings defaultCostModel)
     program

benchClausify :: Clausify.StaticFormula -> Benchmarkable
benchClausify f =
  benchCek $ Clausify.mkClausifyTerm 1 f

benchPrime :: Prime.PrimeID -> Benchmarkable
benchPrime pid =
  benchCek $ Prime.mkPrimeTerm pid

benchQueens :: Integer -> Queens.Algorithm -> Benchmarkable
benchQueens sz alg =
  benchCek $ Queens.mkQueensTerm sz alg

benchKnights :: Integer -> Integer -> Benchmarkable
benchKnights depth sz =
  benchCek $ Knights.mkKnightsTerm depth sz

config :: Config
config = defaultConfig
  { reportFile = Just "report.html"
  , jsonFile   = Just "report.json"
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
main = defaultMainWith config [
    bgroup "clausify" [ bench "formula3" $ benchClausify Clausify.F3
                      , bench "formula4" $ benchClausify Clausify.F4
                      , bench "formula5" $ benchClausify Clausify.F5
                      , bench "formula6" $ benchClausify Clausify.F6
                      , bench "formula7" $ benchClausify Clausify.F7
                      ]
  , bgroup "primetest" [ bench "10-digits" $ benchPrime Prime.P10
                       , bench "20-digits" $ benchPrime Prime.P20
                       , bench "30-digits" $ benchPrime Prime.P30
                       , bench "40-digits" $ benchPrime Prime.P40
                       , bench "50-digits" $ benchPrime Prime.P50
                       , bench "60-digits" $ benchPrime Prime.P60
                       ]
  , bgroup "queens" [ -- N-queens problem on a 5x5 board
                      bench "bt"    $ benchQueens 5 Queens.Bt
                    , bench "bm"    $ benchQueens 5 Queens.Bm
                    , bench "bjbt"  $ benchQueens 5 Queens.Bjbt
                    , bench "bjbt1" $ benchQueens 5 Queens.Bjbt1
                    , bench "fc"    $ benchQueens 5 Queens.Fc
                    ]
  , bgroup "knights" [ -- Knight's tour on an NxN board; no solutions for N odd
                       bench "4x4" $ benchKnights 150 4
                     , bench "5x5" $ benchKnights 150 5
                     , bench "6x6" $ benchKnights 150 6
                     , bench "7x7" $ benchKnights 150 7
                     , bench "8x8" $ benchKnights 150 8
                     ]
       ]
