{- | Plutus benchmarks for some simple list-sorting algortihms. -}

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

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


---------------- Hand-written folds ----------------

mkBuiltinList :: Integer -> Term
mkBuiltinList n = mkConstant @[Integer] () [1..n]

mkPlcSumLeftBuiltin :: Integer -> Term
mkPlcSumLeftBuiltin n = UPLC.Apply () (UPLC.erase BuiltinList.sum) (mkBuiltinList n)

mkPlcSumRightBuiltin :: Integer -> Term
mkPlcSumRightBuiltin n = UPLC.Apply () (UPLC.erase BuiltinList.sumr) (mkBuiltinList n)

mkScottList :: Integer -> Term
mkScottList n = compiledCodeToTerm (Tx.liftCode [1..n])

mkPlcSumLeftScott :: Integer -> Term
mkPlcSumLeftScott n = UPLC.Apply () (UPLC.erase ScottList.sum) (mkScottList n)

mkPlcSumRightScott :: Integer -> Term
mkPlcSumRightScott n = UPLC.Apply () (UPLC.erase ScottList.sumr) (mkScottList n)

---------------- Compiled folds ----------------

mkCompiledSumLeftScott :: Integer -> Term
mkCompiledSumLeftScott n = compiledCodeToTerm $ $$(Tx.compile [|| sumLeftScott ||]) `Tx.applyCode` Tx.liftCode [1..n]

mkCompiledSumRightScott :: Integer -> Term
mkCompiledSumRightScott n = compiledCodeToTerm $ $$(Tx.compile [|| sumRightScott ||]) `Tx.applyCode` Tx.liftCode [1..n]

mkCompiledSumRightBuiltin :: Integer -> Term
mkCompiledSumRightBuiltin n = compiledCodeToTerm $ $$(Tx.compile [|| sumRightBuiltin ||]) `Tx.applyCode` Tx.liftCode (BI.BuiltinList [1..n])

mkCompiledSumLeftBuiltin :: Integer -> Term
mkCompiledSumLeftBuiltin n = compiledCodeToTerm $ $$(Tx.compile [|| sumLeftBuiltin ||]) `Tx.applyCode` Tx.liftCode (BI.BuiltinList [1..n])

benchmarks :: [Benchmark]
benchmarks =
    [ bgroup "sort"
      [ mkBMsForSort "ghcSort"       mkWorstCaseGhcSortTerm
      , mkBMsForSort "insertionSort" mkWorstCaseInsertionSortTerm
      , mkBMsForSort "mergeSort"     mkWorstCaseMergeSortTerm
      , mkBMsForSort "quickSort"     mkWorstCaseQuickSortTerm
      ]
    , bgroup "sum"
     [
      bgroup "compiled-from-Haskell"
        [ mkBMsForSum "sum-builtin-L" mkCompiledSumLeftBuiltin
        , mkBMsForSum "sum-builtin-R" mkCompiledSumRightBuiltin
        , mkBMsForSum "sum-Scott-L"   mkCompiledSumLeftScott
        , mkBMsForSum "sum-Scott-R"   mkCompiledSumRightScott

        ]
      ,
      bgroup "hand-written-PLC"
        [ mkBMsForSum "sum-builtin-L"  mkPlcSumLeftBuiltin
        , mkBMsForSum "sum-builtin-R"  mkPlcSumRightBuiltin
        , mkBMsForSum "sum-Scott-L"    mkPlcSumLeftScott
        , mkBMsForSum "sum-Scott-R"    mkPlcSumRightScott
        ]
      ]
    ]
    where
      mkBMs sizes name f = bgroup name $ map (\n -> bench (show n) . benchTermCek . f $ n) sizes
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
      where go s t =
                do   putStrLn "-----------------------------------------------"
                     putStr s
                     putStrLn . show . PP.prettyPlcClassicDef . eval  $ t 20

