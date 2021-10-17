{- | Plutus benchmarks for some simple list-sorting algortihms. -}

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import           Criterion.Main

import           PlutusBenchmark.ListSort.GhcSort
import           PlutusBenchmark.ListSort.InsertionSort
import           PlutusBenchmark.ListSort.MergeSort
import           PlutusBenchmark.ListSort.QuickSort

import           PlutusBenchmark.Common                   (Term, benchTermCek, compiledCodeToTerm, getConfig)

import qualified PlutusTx                                 as Tx
import qualified PlutusTx.Builtins.Internal               as BI

import           Data.Text                                (Text)
import qualified PlutusCore                               as PLC
import           PlutusCore.MkPlc
import qualified PlutusCore.Pretty                        as PP
import qualified UntypedPlutusCore                        as UPLC
import           UntypedPlutusCore.Evaluation.Machine.Cek as Cek

import           BuiltinFold

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

mkBuiltinList :: Integer -> Term
mkBuiltinList n = mkConstant @[Integer] () [1..n]

mkBuiltinSumL :: Integer -> Term
mkBuiltinSumL n = UPLC.Apply () (UPLC.erase BuiltinList.sum) (mkBuiltinList n)

mkBuiltinSumR :: Integer -> Term
mkBuiltinSumR n = UPLC.Apply () (UPLC.erase BuiltinList.sumR) (mkBuiltinList n)

mkBuiltinSumL2 :: Integer -> Term
mkBuiltinSumL2 n = UPLC.Apply () (UPLC.erase BuiltinList.sumL2) (mkBuiltinList n)

mkBuiltinSumR2 :: Integer -> Term
mkBuiltinSumR2 n = UPLC.Apply () (UPLC.erase BuiltinList.sumR2) (mkBuiltinList n)

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

benchBuiltinSumL2 :: Integer -> Benchmarkable
benchBuiltinSumL2 n = benchTermCek $ mkBuiltinSumL2 n

benchBuiltinSumR2 :: Integer -> Benchmarkable
benchBuiltinSumR2 n = benchTermCek $ mkBuiltinSumR2 n

benchScottSumL :: Integer -> Benchmarkable
benchScottSumL n = benchTermCek $ mkScottSumL n

benchScottSumR :: Integer -> Benchmarkable
benchScottSumR n = benchTermCek $ mkScottSumR n

-- The built-in sum uses a PLC case discriminator. We also want a version using
-- the builtin case, which will require a fold written in Haskell using the Tx-level
-- case builtin.

mkTxSumLeft :: Integer -> Term
mkTxSumLeft n = compiledCodeToTerm $ $$(Tx.compile [|| sumLeft ||]) `Tx.applyCode` Tx.liftCode [1..n]

benchTxSumLeft :: Integer -> Benchmarkable
benchTxSumLeft n = benchTermCek $ mkTxSumLeft n

mkTxSumRight :: Integer -> Term
mkTxSumRight n = compiledCodeToTerm $ $$(Tx.compile [|| sumRight ||]) `Tx.applyCode` Tx.liftCode [1..n]

benchTxSumRight :: Integer -> Benchmarkable
benchTxSumRight n = benchTermCek $ mkTxSumRight n

mkTxSumRightX :: Integer -> Term
mkTxSumRightX n = compiledCodeToTerm $ $$(Tx.compile [|| sumRightX ||]) `Tx.applyCode` Tx.liftCode (BI.BuiltinList [1..n])

benchTxSumRightX :: Integer -> Benchmarkable
benchTxSumRightX n = benchTermCek $ mkTxSumRightX n

mkTxSumLeftX :: Integer -> Term
mkTxSumLeftX n = compiledCodeToTerm $ $$(Tx.compile [|| sumLeftX ||]) `Tx.applyCode` Tx.liftCode (BI.BuiltinList [1..n])

benchTxSumLeftX :: Integer -> Benchmarkable
benchTxSumLeftX n = benchTermCek $ mkTxSumRightX n

benchmarks :: [Benchmark]
benchmarks =
    [ bgroup "sort"
      [ mkBMsForSort "ghcSort"       benchGhcSort
      , mkBMsForSort "insertionSort" benchInsertionSort
      , mkBMsForSort "mergeSort"     benchMergeSort
      , mkBMsForSort "quickSort"     benchQuickSort
      ]
    , bgroup "sum"
     [
      bgroup "compiled-from-Haskell"
        [ mkBMsForSum "sum-builtin-L" benchTxSumLeftX
        , mkBMsForSum "sum-builtin-R" benchTxSumRightX
        , mkBMsForSum "sum-Scott-L"   benchTxSumLeft
        , mkBMsForSum "sum-Scott-R"   benchTxSumRight
        ]
      ,
      bgroup "hand-written-PLC"
        [ mkBMsForSum "sum-builtin-L"  benchBuiltinSumL
        , mkBMsForSum "sum-builtin-R"  benchBuiltinSumR
        , mkBMsForSum "sum-Scott-L"    benchScottSumL
        , mkBMsForSum "sum-Scott-R"    benchScottSumR
        ]
      ]
    ]
    where
      mkBMs sizes name bm = bgroup name $ map (\n -> bench (show n) $ bm n) sizes
      mkBMsForSum = mkBMs [10, 100, 1000, 10000]
      mkBMsForSort= mkBMs [10,20..500]

{- Want sumL and sumR for
  * Scott-encoded lists compiled from Haskell
  * Builtin lists compiled from Haskell
  * Scott-encoded lists, hand-written PLC AST
  * Builtin lists, hand-written PLC AST

  We have all of these, but the hand-written PLC examples for the builtin lists
  use nullList and ifThenElse instead of chooseList.
-}

eval1 :: Term -> (EvaluationResult Term, [Text])
eval1 = Cek.unsafeEvaluateCek Cek.noEmitter PLC.defaultCekParameters

eval2 :: Term -> Term
eval2 = id

eval = eval1

main :: IO ()
main = do
  config <- getConfig 15.0  -- Run each benchmark for at least 15 seconds.  Change this with -L or --timeout.
  defaultMainWith config benchmarks
  go "Builtin sumL:  " mkBuiltinSumL
  go "Builtin sumL2: " mkBuiltinSumL2
  go "Builtin sumR:  " mkBuiltinSumR
  go "Builtin sumR2: " mkBuiltinSumR2
      where go s t =
                do   putStrLn "-----------------------------------------------"
                     putStr s
                     putStrLn . show . PP.prettyPlcClassicDef . eval  $ t 20

