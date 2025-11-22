{-# LANGUAGE OverloadedStrings #-}

{-| This compiles several list-sorting algorithms to Plutus Core and runs them on
   worst-case inputs, reporting the CPU cost in ExUnits. -}
module Main where

import Data.HashMap.Monoidal qualified as H
import Text.Printf (printf)

import PlutusBenchmark.Common (Term)
import PlutusBenchmark.Lists.Sort

import Data.SatInt
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

getBudgetUsage :: Term -> Maybe Integer
getBudgetUsage term =
  case (\(Cek.CekReport fstT sndT _) -> (Cek.cekResultToEither fstT, sndT)) $
    Cek.runCekDeBruijn PLC.defaultCekParametersForTesting Cek.counting Cek.noEmitter term of
    (Left _, _) -> Nothing
    (Right _, Cek.CountingSt c) ->
      let ExCPU cpu = exBudgetCPU c in Just $ fromSatInt cpu

getCekSteps :: Term -> Maybe Integer
getCekSteps term =
  case (\(Cek.CekReport fstT sndT _) -> (Cek.cekResultToEither fstT, sndT)) $
    Cek.runCekDeBruijn PLC.unitCekParameters Cek.tallying Cek.noEmitter term of
    (Left _, _) -> Nothing
    (Right _, Cek.TallyingSt (Cek.CekExTally counts) _) ->
      let getCount k =
            case H.lookup k counts of
              Just v -> let ExCPU n = exBudgetCPU v in fromSatInt n
              Nothing -> 0
          allNodeTags =
            fmap
              Cek.BStep
              [ Cek.BConst
              , Cek.BVar
              , Cek.BLamAbs
              , Cek.BApply
              , Cek.BDelay
              , Cek.BForce
              , Cek.BBuiltin
              ]
          totalComputeSteps = sum $ map getCount allNodeTags
       in Just totalComputeSteps

getInfo :: Term -> Maybe (Integer, Integer)
getInfo term =
  case (getBudgetUsage term, getCekSteps term) of
    (Just c, Just n) -> Just (c, n)
    _ -> Nothing

-- Create a term sorting a list of length n and execute it in counting mode then
-- tallying mode and print out the cost and the number of CEK compute steps.
printSortStatistics :: (Integer -> Term) -> Integer -> IO ()
printSortStatistics termMaker n =
  let term = termMaker n
   in case getInfo term of
        Nothing -> putStrLn "Error during execution"
        Just (cpu, steps) ->
          putStr $
            printf
              "%-4d  %5s ms %16s %14s\n"
              n
              (PLC.show $ cpu `div` 1000000000)
              ("(" ++ PLC.show cpu ++ ")")
              (PLC.show steps)

main :: IO ()
main = do
  let inputLengths = [10, 20 .. 500]
      header =
        "Length  Cost (ms)   Cost (ps)         CEK steps\n"
          ++ "------------------------------------------------"
  putStrLn "GHC sort"
  putStrLn ""
  putStrLn header
  mapM_ (printSortStatistics mkWorstCaseGhcSortTerm) inputLengths
  putStrLn "\n"
  putStrLn "Insertion sort"
  putStrLn ""
  putStrLn header
  mapM_ (printSortStatistics mkWorstCaseInsertionSortTerm) inputLengths
  putStrLn "\n"
  putStrLn "Merge sort"
  putStrLn ""
  putStrLn header
  mapM_ (printSortStatistics mkWorstCaseMergeSortTerm) inputLengths
  putStrLn "\n"
  putStrLn "Quicksort"
  putStrLn ""
  putStrLn header
  mapM_ (printSortStatistics mkWorstCaseQuickSortTerm) inputLengths
