{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Simple quicksort implementation.
module PlutusBenchmark.Lists.Sort.QuickSort where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import PlutusTx qualified as Tx
import PlutusTx.List
import PlutusTx.Plugin ()
import PlutusTx.Prelude as Tx

quickSort :: [Integer] -> [Integer]
quickSort [] = []
quickSort (n : ns) = (quickSort $ before n ns []) ++ (n : (quickSort $ after n ns []))
  where
    before _ [] r = r -- Elements < x
    before x (y : ys) r =
      if y < x
        then before x ys (y : r)
        else before x ys r
    after _ [] r = r
    after x (y : ys) r =
      if y >= x -- Elements >= x
        then after x ys (y : r)
        else after x ys r
{-# INLINEABLE quickSort #-}

{- The worst case is when the list is already sorted (or reverse sorted) because
   then if the list has n elements you have to recurse n times, scanning a list
   of length n-1, n-2, n-3, ... in the left or right branches.  If the list is
   more balanced you recurse log n times, scanning two lists of length (n-1)/2,
   then four of length (n-3)/4, and so on.  For this version a reverse-sorted
   input seems to be marginally slower than a properly-sorted input. -}
quickSortWorstCase :: Integer -> [Integer]
quickSortWorstCase n = reverse [1 .. n]

mkQuickSortTerm :: [Integer] -> Term
mkQuickSortTerm l =
  compiledCodeToTerm $ $$(Tx.compile [||quickSort||]) `Tx.unsafeApplyCode` Tx.liftCodeDef l

mkWorstCaseQuickSortTerm :: Integer -> Term
mkWorstCaseQuickSortTerm = mkQuickSortTerm . quickSortWorstCase
