{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}

{- | Simple quicksort implementation. -}
module PlutusBenchmark.ListSort.QuickSort where

import           PlutusBenchmark.Common (compiledCodeToTerm)

import           PlutusCore.Default
import qualified PlutusTx               as Tx
import           PlutusTx.Prelude       as Tx
import qualified UntypedPlutusCore      as UPLC


{-# INLINABLE quickSort #-}
quickSort :: [Integer] -> [Integer]
quickSort []     = []
quickSort (n:ns) = (quickSort $ before n ns []) ++ (n:(quickSort $ after n ns []))
    where  before _ [] r = r  -- Elements < x
           before x (y:ys) r = if y < x
                           then before x ys (y:r)
                           else before x ys r
           after _ [] r = r
           after x (y:ys) r = if y >= x  -- Elements >= x
                           then after x ys (y:r)
                           else after x ys r

{- The worst case is when the list is already sorted (or reverse sorted) because
   then if the list has n elements you have to recurse n times, scanning a list
   of length n-1, n-2, n-3, ... in the left or right branches.  If the list is
   more balanced you recurse log n times, scanning two lists of length (n-1)/2,
   then four of length (n-3)/4, and so on.  For this version a reverse-sorted
   input seems to be marginally slower than a properly-sorted input. -}
quickSortWorstCase :: Integer -> [Integer]
quickSortWorstCase n = reverse [1..n]

quickSortPlc :: Tx.CompiledCodeIn DefaultUni DefaultFun ([Integer] -> [Integer])
quickSortPlc = $$(Tx.compile [|| quickSort ||])

mkQuickSortTerm :: [Integer] -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkQuickSortTerm l =
    compiledCodeToTerm $ $$(Tx.compile [|| quickSort ||]) `Tx.applyCode` Tx.liftCode l

mkWorstCaseQuickSortTerm :: Integer -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkWorstCaseQuickSortTerm = mkQuickSortTerm . quickSortWorstCase
