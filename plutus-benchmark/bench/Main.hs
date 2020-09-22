module Main where

import           Criterion.Main
import Criterion.Types (Config(..))
import qualified Data.Map                                                   as Map

import           Language.PlutusCore                                        (Name (..))
import           Language.PlutusCore.Constant                               (DynamicBuiltinNameMeanings (..))
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Universe
import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek
import qualified Plutus.Benchmark.Clausify                                  as Clausify

emptyBuiltins :: DynamicBuiltinNameMeanings (CekValue DefaultUni)
emptyBuiltins =  DynamicBuiltinNameMeanings Map.empty

benchCek :: Term Name DefaultUni () -> Benchmarkable
benchCek program =
  nf (unsafeEvaluateCek emptyBuiltins defaultCostModel)
     program

config :: Config
config = defaultConfig 
  { reportFile = Just "report.html"
  , jsonFile = Just "report.json"
  }


main :: IO ()
main = defaultMainWith config [
  bgroup "clausify" [ bench "Formula 5A" $ benchCek (Clausify.mkClausifyTerm 1 Clausify.F5A)
                    , bench "Formula 5"  $ benchCek (Clausify.mkClausifyTerm 1 Clausify.F5)
                    ]
  ]
