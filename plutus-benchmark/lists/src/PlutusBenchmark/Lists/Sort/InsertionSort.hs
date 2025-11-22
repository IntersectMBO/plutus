{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Simple insertion sort implementation
module PlutusBenchmark.Lists.Sort.InsertionSort where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import PlutusTx qualified as Tx
import PlutusTx.Plugin ()
import PlutusTx.Prelude

insertionSort :: [Integer] -> [Integer]
insertionSort l0 = sort l0 []
  where
    sort [] r = r
    sort (n : ns) r = sort ns (insert n r)
    insert n acc =
      case acc of
        [] -> [n]
        m : ms ->
          if n <= m
            then n : acc
            else m : (insert n ms)
{-# INLINEABLE insertionSort #-}

{- The worst case should be when the list is already sorted, since then whenever
   we insert a new element in the accumulator it'll have to go at the very end. -}
insertionSortWorstCase :: Integer -> [Integer]
insertionSortWorstCase n = [1 .. n]

mkInsertionSortTerm :: [Integer] -> Term
mkInsertionSortTerm l =
  compiledCodeToTerm $ $$(Tx.compile [||insertionSort||]) `Tx.unsafeApplyCode` Tx.liftCodeDef l

mkWorstCaseInsertionSortTerm :: Integer -> Term
mkWorstCaseInsertionSortTerm = mkInsertionSortTerm . insertionSortWorstCase
