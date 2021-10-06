{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

{- | This compiles several list-sorting algorithms to Plutus Core and runs them on
   worst-case inputs, reporting the CPU cost in ExUnits. -}

module Main where

import           Control.Exception
import           Control.Monad.Trans.Except
import qualified Data.HashMap.Monoidal                    as H
import           Text.Printf                              (printf)

import           InsertionSort
import           MergeSort
import           QuickSort

import           PlutusCore                               (Name (..))
import qualified PlutusCore                               as PLC
import           PlutusCore.Default
import           PlutusCore.Evaluation.Machine.ExBudget   (ExBudget (..))
import           PlutusCore.Evaluation.Machine.ExMemory
import qualified UntypedPlutusCore                        as UPLC
import qualified UntypedPlutusCore.Evaluation.Machine.Cek as Cek

getUnDBrTerm
    :: UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
    -> UPLC.Term Name DefaultUni DefaultFun ()
getUnDBrTerm term =
    case runExcept @UPLC.FreeVariableError . PLC.runQuoteT . UPLC.unDeBruijnTerm $ term of
      Left e  -> throw e
      Right t -> t

getBudgetUsage
    :: UPLC.Term Name DefaultUni DefaultFun ()
    -> Maybe Integer
getBudgetUsage term =
    case Cek.runCekNoEmit PLC.defaultCekParameters Cek.counting term of
      (Left _, _)                 -> Nothing
      (Right _, Cek.CountingSt c) -> let ExCPU cpu = exBudgetCPU c in Just $ fromIntegral cpu

getCekSteps
    :: UPLC.Term Name DefaultUni DefaultFun ()
    -> Maybe Integer
getCekSteps term =
    case Cek.runCekNoEmit PLC.unitCekParameters Cek.tallying term of
      (Left _, _)                   -> Nothing
      (Right _, Cek.TallyingSt (Cek.CekExTally counts) _) ->
          let getCount k =
                  case H.lookup k counts of
                    Just v  -> let ExCPU n = exBudgetCPU v in fromIntegral n
                    Nothing -> 0
              allNodeTags = fmap Cek.BStep [Cek.BConst, Cek.BVar, Cek.BLamAbs, Cek.BApply, Cek.BDelay, Cek.BForce, Cek.BBuiltin]
              totalComputeSteps = sum $ map getCount allNodeTags
          in Just totalComputeSteps

getInfo :: UPLC.Term Name DefaultUni DefaultFun ()
    -> Maybe (Integer, Integer)
getInfo term =
    case (getBudgetUsage term, getCekSteps term) of
      (Just c, Just n) -> Just (c,n)
      _                -> Nothing



runSort :: Integer -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun () -> IO ()
runSort n term =
    let term' = getUnDBrTerm term
    in case getInfo term' of
         Nothing -> putStrLn "Error during execution"
         Just (cpu, steps) ->
           putStr $ printf "%-4d  %5s ms %16s %14s\n"
                  n
                  (PLC.show $ cpu`div` 1000000000)
                  ("(" ++ PLC.show cpu ++ ")")
                  (PLC.show steps)


main :: IO ()
main = do
  let inputLengths = [10,20..400]
      header = "Length  Cost (ms)   Cost (ps)         CEK steps\n"
            ++ "------------------------------------------------"
  putStrLn "Insertion sort"
  putStrLn ""
  putStrLn header
  mapM_ (\n -> runSort n (mkInsertionSortTerm n)) inputLengths
  putStrLn "\n"
  putStrLn "Merge sort"
  putStrLn ""
  putStrLn header
  mapM_ (\n -> runSort n $ mkMergeSortTerm n) inputLengths
  putStrLn "\n"
  putStrLn "Quicksort"
  putStrLn ""
  putStrLn header
  mapM_ (\n -> runSort n (mkQuickSortTerm n)) inputLengths

