{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

-- | Simple merge sort implementation
module PlutusBenchmark.Lists.Sort.MergeSort where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import PlutusTx qualified as Tx
import PlutusTx.List
import PlutusTx.Plugin ()
import PlutusTx.Prelude as Tx

merge :: [Integer] -> [Integer] -> [Integer]
merge as@(a : as') bs@(b : bs') =
  if a <= b
    then a : (merge as' bs)
    else b : (merge as bs')
merge [] bs = bs
merge as [] = as
{-# INLINEABLE merge #-}

mergeSort :: [Integer] -> [Integer]
mergeSort xs =
  let n = length xs
   in if n > 1
        then
          let n2 = n `divide` 2
           in merge (mergeSort (take n2 xs)) (mergeSort (drop n2 xs))
        else xs
{-# INLINEABLE mergeSort #-}

{- I think this is approximately the worst case.  A lot of the work happens in
   merge and this should make sure that the maximal amount of interleaving is
   required there.  If we merge [1,2,3,4] and [5,6,7,8] then we get to the case
   merge [] [5,6,7,8] which can return immediately; this function at n=8 gives us
   [1,5,3,7,2,6,4,8], which leads to merge [1,3,5,7] [2,4,6,8], and we have to go
   all the way to 1:2:3:4:5:6:7:(merge [] [8]) to merge those. -}
mergeSortWorstCase :: Integer -> [Integer]
mergeSortWorstCase n = f [1 .. n]
  where
    f ls =
      let (left, right) = unzip2 ls [] []
       in case (left, right) of
            ([], _) -> right
            (_, []) -> left
            _ -> f left ++ f right
    unzip2 l lacc racc =
      case l of
        [] -> (reverse lacc, reverse racc)
        [a] -> (reverse (a : lacc), reverse racc)
        (a : b : rest) -> unzip2 rest (a : lacc) (b : racc)

mkMergeSortTerm :: [Integer] -> Term
mkMergeSortTerm l =
  compiledCodeToTerm $ $$(Tx.compile [||mergeSort||]) `Tx.unsafeApplyCode` Tx.liftCodeDef l

mkWorstCaseMergeSortTerm :: Integer -> Term
mkWorstCaseMergeSortTerm = mkMergeSortTerm . mergeSortWorstCase
