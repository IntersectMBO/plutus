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
  benchCek (Clausify.mkClausifyTerm 1 f)

benchPrime :: [Integer] -> Benchmark
benchPrime ns =
  bench (" " <> show ns) $ benchCek (Prime.mkPrimeTerm ns)

config :: Config
config = defaultConfig
  { reportFile = Just "report.html"
  , jsonFile = Just "report.json"
  }

main :: IO ()
main = defaultMainWith config [
    bgroup "clausify" [ bench "formula3" $ (benchClausify Clausify.F3)
                      , bench "formula4" $ (benchClausify Clausify.F4)
                      , bench "formula5" $ (benchClausify Clausify.F5)
                      , bench "formula6" $ (benchClausify Clausify.F6)
                      , bench "formula7" $ (benchClausify Clausify.F7)
                      ]
  , bgroup "queens" [ bench " 5x5 with bt, bm, bjbt, bjbt' and Fc" $
                        benchCek ( Queens.mkQueensTerm 5
                                 [ Queens.Bt
                                 , Queens.Bm
                                 , Queens.Bjbt
                                 , Queens.Bjbt'
                                 , Queens.Fc ]
                                 ) ]
  , bgroup "knights" [ bench " 150 depth, 5x5 board" $
                         benchCek ( Knights.mkKnightsTerm 150 5 ) ]
  , bgroup "primes" [ benchPrime [115756986668303657898962467957]
                    , benchPrime [8987964267331664557]
                    , benchPrime [444, 4, 17331, 17, 1929475734529795, 95823752743877]
                    , benchPrime [9576890767]
                    , benchPrime [40206835204840513073]
                    , benchPrime [115756986668303657898962467957]
                    , benchPrime [671998030559713968361666935769]
                    , benchPrime [4125636888562548868221559797461449]
                    , benchPrime [5991810554633396517767024967580894321153]
                    , benchPrime [22953686867719691230002707821868552601124472329079]
                    , benchPrime [48705091355238882778842909230056712140813460157899]
                    , benchPrime [511704374946917490638851104912462284144240813125071454126151]
                    , benchPrime [511704374946917490638851104912462284144240813125071454126151]
                  ]
  ]
