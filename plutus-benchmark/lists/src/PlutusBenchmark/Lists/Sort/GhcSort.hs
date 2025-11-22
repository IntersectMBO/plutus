{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Merge sort implementation based on GHC's 'sort' function
module PlutusBenchmark.Lists.Sort.GhcSort where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)
import PlutusBenchmark.Lists.Sort.MergeSort (mergeSortWorstCase)

import PlutusTx qualified as Tx
import PlutusTx.Plugin ()
import PlutusTx.Prelude as Tx

{-| GHC's 'sort' algorithm specialised to Integer.
   See https://hackage.haskell.org/package/base-4.15.0.0/docs/src/Data-OldList.html#sortBy -}
ghcSort :: [Integer] -> [Integer]
ghcSort = mergeAll . sequences
  where
    sequences (a : b : xs)
      | a > b = descending b [a] xs
      | otherwise = ascending b (a :) xs
    sequences xs = [xs]
    {- This detects ascending and descending subsequences of a list, reverses
       the descending ones, and accumulates the results in a list.
       For example, [1,2,9,5,4,7,2,8] -> [[1,2,9],[4,5],[2,7],[8]]. -}

    descending a as (b : bs)
      | a > b = descending b (a : as) bs
    descending a as bs = (a : as) : sequences bs

    ascending a as (b : bs)
      | a <= b = ascending b (\ys -> as (a : ys)) bs
    ascending a as bs =
      let !x = as [a]
       in x : sequences bs

    mergeAll [x] = x
    mergeAll xs = mergeAll (mergePairs xs)

    mergePairs (a : b : xs) =
      let !x = merge a b
       in x : mergePairs xs
    mergePairs xs = xs
    {- Merge adjoining pairs of ordered lists to get a new list of ordered lists then
       recurse on that; we're doing a kind of binary tree of merges, and I think
       that this (maybe along with some benefits from laziness when we're
       running this in Haskell) is what makes this algorithm faster than
       standard mergesort. -}

    merge as@(a : as') bs@(b : bs') =
      -- Same as in mergeSort
      if a <= b
        then a : (merge as' bs)
        else b : (merge as bs')
    merge [] bs = bs
    merge as [] = as
{-# INLINEABLE ghcSort #-}

{- I think the worst case input should be about the same as for mergesort.  The
   worst case for 'sequences' is when we start with a list of alternately
   increasing and decreasing elements, which yields a list of two-element lists.
   Given this, we want to make sure that mergePairs does as much work as
   possible, so we want maximal interleaving at all levels, for example
   [[1,5],[3,7],[2,6],[4,8] -> [[1,3,5,7], [2,6,4,8]] -> [[1,2,3,4,5,6,7,8]].
   This is what mergeSortWorstCase does.  We appear to get slightly worse
   behaviour (by a percent or two) if we reverse the list: if we do that then
   we're always in the descending case, but it's not obvious why that would be
   worse than the ascending case.  Experiments on random lists suggest that the
   behaviour for both ghcSort and mergeSort on the output of mergeSortWorstCase
   is only 3% or 4% worse than the average case. -}
ghcSortWorstCase :: Integer -> [Integer]
ghcSortWorstCase = mergeSortWorstCase

mkGhcSortTerm :: [Integer] -> Term
mkGhcSortTerm l =
  compiledCodeToTerm $ $$(Tx.compile [||ghcSort||]) `Tx.unsafeApplyCode` Tx.liftCodeDef l

mkWorstCaseGhcSortTerm :: Integer -> Term
mkWorstCaseGhcSortTerm = mkGhcSortTerm . ghcSortWorstCase
