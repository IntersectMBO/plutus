{-# LANGUAGE ViewPatterns #-}

module Main where

import Control.Exception
import Criterion.Main
import Data.SatInt
import PlutusBenchmark.Common (benchTermCek, compiledCodeToTerm, getConfig, mkMostRecentEvalCtx)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusLedgerApi.Common (EvaluationContext)
import PlutusTx.Code
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import PlutusBenchmark.SOP.Big.Scott qualified as ScottBig
import PlutusBenchmark.SOP.Big.SOP qualified as SOPBig
import PlutusBenchmark.SOP.Common
import PlutusBenchmark.SOP.List.Scott qualified as ScottList
import PlutusBenchmark.SOP.List.SOP qualified as SOPList

getBudgetUsage :: CompiledCode a -> Maybe (Integer, Integer, Integer)
getBudgetUsage (compiledCodeToTerm -> term) =
    case (\(Cek.CekReport fstT sndT _) -> (Cek.cekResultToEither fstT, sndT)) $
      Cek.runCekDeBruijn PLC.defaultCekParametersForTesting Cek.counting Cek.noEmitter term
    of
      (Left _, _)                 -> Nothing
      (Right _, Cek.CountingSt c) ->
          let
            ExCPU (fromSatInt -> cpu) = exBudgetCPU c
            ExMemory (fromSatInt -> mem) = exBudgetMemory c
          in Just $ (cpu, mem, UPLC.unAstSize $ UPLC.termAstSize term)

printBudget :: String -> CompiledCode a -> IO ()
printBudget name c =
  case getBudgetUsage c of
    Nothing -> putStrLn $ name <> " evaluation failed"
    Just (cpu, mem, size) -> do
      -- print $ pretty $ getPlcNoAnn c
      putStrLn $ name <> ", " <> show cpu <> ", " <> show mem <> ", " <> show size

benchmarks :: EvaluationContext -> [Benchmark]
benchmarks ctx =
  let
    sopList :: CompiledCode (SOPList.SOPList Integer)
    sopList =
      SOPList.replicateSOPList
        `app` (liftCode110Norm 50)
        `app` (liftCode110Norm 42)

    scottList :: CompiledCode (ScottList.ScottList Integer)
    scottList =
      ScottList.replicateScottList
        `app` (liftCode110Norm 50)
        `app` (liftCode110Norm 42)

    sumSopList :: CompiledCode Integer
    sumSopList =
      SOPList.sumSOPList
        `app` (normCompiledCode sopList)

    sumScottList :: CompiledCode Integer
    sumScottList =
      ScottList.sumScottList
        `app` (normCompiledCode scottList)

    bigNest = 10

    sopBig :: CompiledCode SOPBig.SOPBig
    sopBig =
      SOPBig.mkSOPBigFull
        `app` (liftCode110Norm bigNest)
        `app` (liftCode110Norm 42)

    scottBig :: CompiledCode ScottBig.ScottBig
    scottBig =
      ScottBig.mkScottBigFull
        `app` (liftCode110Norm bigNest)
        `app` (liftCode110Norm 42)

    sumSopBig :: CompiledCode Integer
    sumSopBig =
      SOPBig.sumSOPBig
        `app` (normCompiledCode sopBig)

    sumScottBig :: CompiledCode Integer
    sumScottBig =
      ScottBig.sumScottBig
        `app` (normCompiledCode scottBig)
  in [ bgroup "List, replicate 50"
       [ bench "scott" $ benchTermCek ctx (UPLC._progTerm $ getPlcNoAnn scottList)
       , bench "sop" $ benchTermCek ctx (UPLC._progTerm $ getPlcNoAnn sopList)
       ]
     , bgroup "List, sum"
       [ bench "scott" $ benchTermCek ctx (UPLC._progTerm $ getPlcNoAnn sumScottList)
       , bench "sop" $ benchTermCek ctx (UPLC._progTerm $ getPlcNoAnn sumSopList)
       ]
     , bgroup ("Big, replicate " <> show bigNest)
       [ bench "scott" $ benchTermCek ctx (UPLC._progTerm $ getPlcNoAnn scottBig)
       , bench "sop" $ benchTermCek ctx (UPLC._progTerm $ getPlcNoAnn sopBig)
       ]
     , bgroup "Big, sum "
       [ bench "scott" $ benchTermCek ctx (UPLC._progTerm $ getPlcNoAnn sumScottBig)
       , bench "sop" $ benchTermCek ctx (UPLC._progTerm $ getPlcNoAnn sumSopBig)
       ]
     ]

main :: IO ()
main = do
  -- Run each benchmark for at least 15 seconds.  Change this with -L or --timeout.
  config <- getConfig 15.0
  evalCtx <- evaluate mkMostRecentEvalCtx
  defaultMainWith config $ benchmarks evalCtx
