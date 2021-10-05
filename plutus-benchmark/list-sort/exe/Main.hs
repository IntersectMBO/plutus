{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

module Main where

import           Control.Exception
import           Control.Monad.Trans.Except
import           Text.Printf                              (printf)

import           InsertionSort
import           MergeSort
import           QuickSort

import           PlutusCore                               (Name (..))
import qualified PlutusCore                               as PLC
import           PlutusCore.Default
import           PlutusCore.Evaluation.Machine.ExBudget   (ExBudget (..))
import           PlutusCore.Evaluation.Machine.ExMemory   (ExCPU (..))
import qualified UntypedPlutusCore                        as UPLC
import qualified UntypedPlutusCore.Evaluation.Machine.Cek as Cek


getUnDBrTerm
    :: UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
    -> UPLC.Term Name DefaultUni DefaultFun ()
getUnDBrTerm term =
    case runExcept @UPLC.FreeVariableError . PLC.runQuoteT . UPLC.unDeBruijnTerm $ term of
      Left e  -> throw e
      Right t -> t

evaluateWithCek
    :: UPLC.Term Name DefaultUni DefaultFun ()
    -> ( Either (Cek.CekEvaluationException DefaultUni DefaultFun)
                (UPLC.Term Name DefaultUni DefaultFun ())
       , Cek.CountingSt)
evaluateWithCek = Cek.runCekNoEmit PLC.defaultCekParameters Cek.counting

runSort :: Integer -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun () -> IO ()
runSort n term =
    case evaluateWithCek $ getUnDBrTerm term  of
      (Left _, _)  -> putStrLn "Error"
      (Right _, Cek.CountingSt c) ->
          let ExCPU cpu = exBudgetCPU c
          in putStr $ printf "%-4d %s\n" n (PLC.show $ cpu`div` 1000000)

main :: IO ()
main = do
  let inputLengths = [100,200..1000]
  putStrLn "Mergesort"
  putStrLn "---------"
  mapM_ (\n -> runSort n $ mkMergeSortTerm n) inputLengths
  putStrLn "\n"
  putStrLn "Insertion sort"
  putStrLn "--------------"
  mapM_ (\n -> runSort n (mkInsertionSortTerm n)) inputLengths
  putStrLn "\n"
  putStrLn "Quicksort"
  putStrLn "---------"
  mapM_ (\n -> runSort n (mkQuickSortTerm n)) inputLengths

