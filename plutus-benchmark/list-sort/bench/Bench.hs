{- | Plutus benchmarks for some simple list-sorting algortihms. -}

{-# LANGUAGE TypeApplications #-}

module Main where

import           Criterion.Main

import           PlutusBenchmark.ListSort.GhcSort
import           PlutusBenchmark.ListSort.InsertionSort
import           PlutusBenchmark.ListSort.MergeSort
import           PlutusBenchmark.ListSort.QuickSort

import           PlutusBenchmark.Common                   (Term, benchTermCek, compiledCodeToTerm, getConfig)

import qualified PlutusTx                                 as Tx

import           Data.Text                                (Text)
import qualified PlutusCore                               as PLC
import           PlutusCore.MkPlc
import qualified PlutusCore.Pretty                        as PP
import qualified UntypedPlutusCore                        as UPLC
import           UntypedPlutusCore.Evaluation.Machine.Cek as Cek


import qualified PlutusCore.StdLib.Data.List              as BuiltinList
import qualified PlutusCore.StdLib.Data.ScottList         as ScottList

benchGhcSort :: Integer -> Benchmarkable
benchGhcSort n = benchTermCek $ mkWorstCaseGhcSortTerm n

benchInsertionSort :: Integer -> Benchmarkable
benchInsertionSort n = benchTermCek $ mkWorstCaseInsertionSortTerm n

benchMergeSort :: Integer -> Benchmarkable
benchMergeSort n = benchTermCek $ mkWorstCaseMergeSortTerm n

benchQuickSort :: Integer -> Benchmarkable
benchQuickSort n = benchTermCek $ mkWorstCaseQuickSortTerm n

eval :: Term -> (EvaluationResult Term, [Text])
eval = Cek.unsafeEvaluateCek Cek.noEmitter PLC.defaultCekParameters

mkBuiltinList :: Integer -> Term
mkBuiltinList n = mkConstant @[Integer] () [1..n]

mkBuiltinSumL :: Integer -> Term
mkBuiltinSumL n = UPLC.Apply () (UPLC.erase BuiltinList.sum) (mkBuiltinList n)

mkBuiltinSumR :: Integer -> Term
mkBuiltinSumR n = UPLC.Apply () (UPLC.erase BuiltinList.sumR) (mkBuiltinList n)

mkScottList :: Integer -> Term
mkScottList n = compiledCodeToTerm (Tx.liftCode [1..n])

mkScottSumL :: Integer -> Term
mkScottSumL n = UPLC.Apply () (UPLC.erase ScottList.sum) (mkScottList n)

mkScottSumR :: Integer -> Term
mkScottSumR n = UPLC.Apply () (UPLC.erase ScottList.sumR) (mkScottList n)

benchBuiltinSumL :: Integer -> Benchmarkable
benchBuiltinSumL n = benchTermCek $ mkBuiltinSumL n

benchBuiltinSumR :: Integer -> Benchmarkable
benchBuiltinSumR n = benchTermCek $ mkBuiltinSumR n

benchScottSumL :: Integer -> Benchmarkable
benchScottSumL n = benchTermCek $ mkScottSumL n

benchScottSumR :: Integer -> Benchmarkable
benchScottSumR n = benchTermCek $ mkScottSumR n

benchmarks :: [Benchmark]
benchmarks =
    [ bgroup "sort" $
      [ bgroup "ghcSort"       $ map (\n -> bench (show n) $ benchGhcSort n)       sizesForSort
      , bgroup "insertionSort" $ map (\n -> bench (show n) $ benchInsertionSort n) sizesForSort
      , bgroup "mergeSort"     $ map (\n -> bench (show n) $ benchMergeSort n)     sizesForSort
      , bgroup "quickSort"     $ map (\n -> bench (show n) $ benchQuickSort n)     sizesForSort
      ]
    , bgroup "sum" $
      [ bgroup "builtin-sum-L" $ map (\n -> bench (show n) $ benchBuiltinSumL n) sizesForSum
      , bgroup "builtin-sum-R" $ map (\n -> bench (show n) $ benchBuiltinSumR n) sizesForSum
      , bgroup "Scott-sum-L"   $ map (\n -> bench (show n) $ benchScottSumL n)   sizesForSum
      , bgroup "Scott-sum-R"   $ map (\n -> bench (show n) $ benchScottSumR n)   sizesForSum
      ]
    ]
    where
      sizesForSort = [10,20..500]
      sizesForSum  = [10, 100, 1000, 10000]

main :: IO ()
main = do
  config <- getConfig 15.0  -- Run each benchmark for at least 15 seconds.  Change this with -L or --timeout.
  defaultMainWith config benchmarks
  putStrLn "-----------------------------------------------"
  putStr "Scott sumL:    "
  putStrLn . show . PP.prettyPlcClassicDef $ eval $ mkScottSumL 50
  putStrLn "-----------------------------------------------"
  putStr "Scott sumR:    "
  putStrLn . show . PP.prettyPlcClassicDef $ eval $ mkBuiltinSumL 50
  putStrLn "-----------------------------------------------"
  putStr "Builtin sumL:  "
  putStrLn . show . PP.prettyPlcClassicDef $ eval $ mkScottSumR 50
  putStrLn "-----------------------------------------------"
  putStr "Builtin sumR:  "
  putStrLn . show . PP.prettyPlcClassicDef $ eval $ mkBuiltinSumR 50
