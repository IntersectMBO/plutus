{-# LANGUAGE TypeApplications #-}

{- | Plutus benchmarks for some simple list-sorting algortihms. -}
module Main where

import           Control.Exception
import           Control.Monad.Except
import           Criterion.Main
import           Criterion.Types                          (Config (..))
import           System.FilePath

import           InsertionSort
import           MergeSort
import           QuickSort

import           Paths_plutus_benchmark                   (getDataFileName)
import qualified PlutusCore                               as PLC
import           PlutusCore.Default

import           UntypedPlutusCore
import           UntypedPlutusCore.Evaluation.Machine.Cek

-- Criterion configuration
getConfig :: Double -> IO Config
getConfig limit = do
  templateDir <- getDataFileName "templates"
  let templateFile = templateDir </> "with-iterations" <.> "tpl" -- Include number of iterations in HTML report
  pure $ defaultConfig {
                template = templateFile,
                reportFile = Just "report.html",
                timeLimit = limit
              }

benchCek :: Term NamedDeBruijn DefaultUni DefaultFun () -> Benchmarkable
benchCek t = case runExcept @PLC.FreeVariableError $ PLC.runQuoteT $ unDeBruijnTerm t of
    Left e   -> throw e
    Right t' -> nf (unsafeEvaluateCek noEmitter PLC.defaultCekParameters) t'

benchGhcSort :: Integer -> Benchmarkable
benchGhcSort n = benchCek $ mkWorstCaseGhcSortTerm n

benchInsertionSort :: Integer -> Benchmarkable
benchInsertionSort n = benchCek $ mkWorsCaseInsertionSortTerm n

benchMergeSort :: Integer -> Benchmarkable
benchMergeSort n = benchCek $ mkWorstCaseMergeSortTerm n

benchQuickSort :: Integer -> Benchmarkable
benchQuickSort n = benchCek $ mkWorstCaseQuickSortTerm n

benchmarks :: [Benchmark]
benchmarks =
    [
      bgroup "insertionSort" $ map (\n -> bench (show n) $ benchInsertionSort n) sizes
    , bgroup "mergeSort"     $ map (\n -> bench (show n) $ benchMergeSort n)     sizes
    , bgroup "quickSort"     $ map (\n -> bench (show n) $ benchQuickSort n)     sizes
    ]
    where sizes = [10,20..500]

main :: IO ()
main = do
  config <- getConfig 15.0  -- Run each benchmark for at least 15 seconds.  Change this with -L or --timeout.
  defaultMainWith config benchmarks
