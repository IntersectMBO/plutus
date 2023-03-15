{- | Plutus benchmarks for some simple list algorithms.  See README.md for more information. -}

module Main (main) where

import Criterion.Main

import PlutusBenchmark.Common (benchTermCek, getConfig)

import PlutusBenchmark.Lists.Sort qualified as Sort

import PlutusBenchmark.Lists.Sum.Compiled qualified as Sum.Compiled
import PlutusBenchmark.Lists.Sum.HandWritten qualified as Sum.HandWritten

benchmarks :: [Benchmark]
benchmarks =
    [ bgroup "sort"
      [ mkBMsForSort "ghcSort"       Sort.mkWorstCaseGhcSortTerm
      , mkBMsForSort "insertionSort" Sort.mkWorstCaseInsertionSortTerm
      , mkBMsForSort "mergeSort"     Sort.mkWorstCaseMergeSortTerm
      , mkBMsForSort "quickSort"     Sort.mkWorstCaseQuickSortTerm
      ]
    , bgroup "sum"
      [ bgroup "compiled-from-Haskell"
        [ mkBMsForSum "sum-right-builtin" Sum.Compiled.mkSumRightBuiltinTerm
        , mkBMsForSum "sum-right-Scott"   Sum.Compiled.mkSumRightScottTerm
        , mkBMsForSum "sum-right-data"    Sum.Compiled.mkSumRightDataTerm
        , mkBMsForSum "sum-left-builtin"  Sum.Compiled.mkSumLeftBuiltinTerm
        , mkBMsForSum "sum-left-Scott"    Sum.Compiled.mkSumLeftScottTerm
        , mkBMsForSum "sum-left-data"     Sum.Compiled.mkSumLeftDataTerm
       ]
      , bgroup "hand-written-PLC"
        [ mkBMsForSum "sum-right-builtin" Sum.HandWritten.mkSumRightBuiltinTerm
        , mkBMsForSum "sum-right-Scott"   Sum.HandWritten.mkSumRightScottTerm
        , mkBMsForSum "sum-left-builtin"  Sum.HandWritten.mkSumLeftBuiltinTerm
        , mkBMsForSum "sum-left-Scott"    Sum.HandWritten.mkSumLeftScottTerm
        ]
      ]
    ]
    where
      mkBMsForSort name f =
        bgroup name $ map (\n -> bench (show n) . benchTermCek . f $ n) sizesForSort
      sizesForSort = [10, 20..500]
      mkBMsForSum name f =
        bgroup name $ map (\n -> bench (show n) . benchTermCek . f $ [1..n]) sizesForSum
      sizesForSum = [10, 50, 100, 500, 1000, 5000, 10000]

main :: IO ()
main = do
  -- Run each benchmark for at least 15 seconds.  Change this with -L or --timeout.
  config <- getConfig 15.0
  defaultMainWith config benchmarks

