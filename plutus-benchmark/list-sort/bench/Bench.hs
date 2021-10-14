{- | Plutus benchmarks for some simple list-sorting algortihms. -}

{-# LANGUAGE TypeApplications #-}

module Main where

import           Criterion.Main

import           PlutusBenchmark.ListSort.GhcSort
import           PlutusBenchmark.ListSort.InsertionSort
import           PlutusBenchmark.ListSort.MergeSort
import           PlutusBenchmark.ListSort.QuickSort

import           PlutusBenchmark.Common                 (benchTermCek, getConfig)

benchGhcSort :: Integer -> Benchmarkable
benchGhcSort n = benchTermCek $ mkWorstCaseGhcSortTerm n

benchInsertionSort :: Integer -> Benchmarkable
benchInsertionSort n = benchTermCek $ mkWorstCaseInsertionSortTerm n

benchMergeSort :: Integer -> Benchmarkable
benchMergeSort n = benchTermCek $ mkWorstCaseMergeSortTerm n

benchQuickSort :: Integer -> Benchmarkable
benchQuickSort n = benchTermCek $ mkWorstCaseQuickSortTerm n

benchmarks :: [Benchmark]
benchmarks =
    [ bgroup "sort" $
      [ bgroup "ghcSort"       $ map (\n -> bench (show n) $ benchGhcSort n)       sizesForSort
      , bgroup "insertionSort" $ map (\n -> bench (show n) $ benchInsertionSort n) sizesForSort
      , bgroup "mergeSort"     $ map (\n -> bench (show n) $ benchMergeSort n)     sizesForSort
      , bgroup "quickSort"     $ map (\n -> bench (show n) $ benchQuickSort n)     sizesForSort
      ]
    ]
    where
      sizesForSort = [10,20..500]

main :: IO ()
main = do
  config <- getConfig 15.0  -- Run each benchmark for at least 15 seconds.  Change this with -L or --timeout.
  defaultMainWith config benchmarks
