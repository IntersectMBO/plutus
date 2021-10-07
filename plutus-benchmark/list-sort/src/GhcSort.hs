{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}

{-# OPTIONS_GHC -fno-warn-identities              #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds      #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns     #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

{- | Merge sort implementation based on GHC's 'sort' function -}
module GhcSort where

import           MergeSort          (mergeSortWorstCase)

import           PlutusCore.Default
import qualified PlutusTx           as Tx
import           PlutusTx.Prelude   as Tx
import qualified UntypedPlutusCore  as UPLC

{- | GHC's 'sort' algorithm specialised to Integer.
   See https://hackage.haskell.org/package/base-4.15.0.0/docs/src/Data-OldList.html#sortBy
-}
{-# INLINABLE ghcSort #-}
ghcSort :: [Integer] -> [Integer]
ghcSort = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a > b = descending b [a]  xs
      | otherwise       = ascending  b (a:) xs
    sequences xs = [xs]
    {- This detects ascending and descending subsequences of a list, reverses
       the descending ones, and accumulates the results in a list.
       For example, [1,2,9,5,4,7,2,8] -> [[1,2,9],[4,5],[2,7],[8]]. -}

    descending a as (b:bs)
      | a > b = descending b (a:as) bs
    descending a as bs  = (a:as): sequences bs

    ascending a as (b:bs)
      | a <= b = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs   = let !x = as [a]
                          in x : sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = let !x = merge a b
                          in x : mergePairs xs
    mergePairs xs       = xs
    {- Merge adjoining pairs of ordered lists to get a new list of ordered lists then
       recurse on that; we're doing a kind of binary tree of merges. -}

    merge as@(a:as') bs@(b:bs') =  -- Same as in mergeSort
        if a <= b
        then a:(merge as'  bs)
        else b:(merge as bs')
    merge [] bs = bs
    merge as [] = as

{- I think the worst case should be the same as for mergesort.  We start with a
   list of alternately increasing and decreasing elements and 'sequences' gives
   us a list of two-element lists. We then need to make sure that mergePairs
   does as much work as possible, so we want interleaving to occur at all
   levels, eg [[1,5],[3,7],[2,6],[4,8] -> [[1,3,5,7], [2,6,4,8]] ->
   [[1,2,3,4,5,6,7,8]].  This is what mergeSortWorstCase does.  -}
ghcSortWorstCase :: Integer -> [Integer]
ghcSortWorstCase = mergeSortWorstCase

mkGhcSortTerm :: [Integer] -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkGhcSortTerm l =
    let (UPLC.Program _ _ code) = Tx.getPlc $ $$(Tx.compile [|| ghcSort ||]) `Tx.applyCode` Tx.liftCode l
    in code

mkWorstCaseGhcSortTerm :: Integer -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkWorstCaseGhcSortTerm = mkGhcSortTerm . ghcSortWorstCase

