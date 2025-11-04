{-# LANGUAGE ViewPatterns #-}

module Main where

import Data.SatInt
import PlutusBenchmark.Common (compiledCodeToTerm)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Pretty
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

main :: IO ()
main = do
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

  putStrLn "List, replicate 50"
  printBudget "SOP" sopList
  printBudget "Scott" scottList

  putStrLn "List, sum"
  printBudget "SOP" sumSopList
  printBudget "Scott" sumScottList

  putStrLn $ "Big, replicate " <> show bigNest
  printBudget "SOP" sopBig
  printBudget "Scott" scottBig

  putStrLn "Big, sum"
  printBudget "SOP" sumSopBig
  printBudget "Scott" sumScottBig
