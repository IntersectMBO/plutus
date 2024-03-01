-- editorconfig-checker-disable-file
{-# LANGUAGE ViewPatterns #-}
module PlutusTx.SortedMap.Tests (propertyTests) where

import Data.Function qualified as Haskell
import Data.List qualified as Haskell
import Prelude qualified as Haskell

import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Prelude as Tx
import PlutusTx.SortedMap qualified as SortedMap
import Test.Tasty hiding (after)
import Test.Tasty.QuickCheck

-- | tests that merge sort yields the same results as insertion sort *FOR DEDUPS*
equivSortsNoDuplPoly :: (Tx.Ord a, Haskell.Eq a, Haskell.Eq b, Haskell.Show a, Haskell.Show b) => [(a, b)] -> Property
equivSortsNoDuplPoly (AssocMap.fromListSafe -> assocmap) =
    -- note: fromListSafe dedupes the alist
    let resI = SortedMap.insertionSortDeDup assocmap
        resM = SortedMap.mergeSort assocmap
    in conjoin [ property $ SortedMap.isValid resI
               , property $ SortedMap.isValid resM
               -- this property is actually stronger than the 2 above
               , resI === resM
               ]

insertionSortFixesValidityPoly :: (Tx.Ord a) => [(a, b)] -> Property
insertionSortFixesValidityPoly (AssocMap.fromList -> assocmap) =
    not (SortedMap.isValid $ SortedMap.fromMapUnsafe assocmap)
    ==> SortedMap.isValid $ SortedMap.insertionSortDeDup assocmap

mergeSortPreservesDuplicatesPoly :: (Tx.Ord a, Eq b) => [(a, b)] -> Property
mergeSortPreservesDuplicatesPoly alist =
    -- this means that it contains-duplicates
    alist /= Haskell.nubBy ((==) `Haskell.on` fst) alist
    ==>
    let assocmap = AssocMap.fromList alist -- will still contain duplicates
        before = SortedMap.isValid $ SortedMap.fromMapUnsafe assocmap
        after = SortedMap.isValid $ SortedMap.mergeSort assocmap
    in before === False .&&.
       after === False

deletesAllPoly :: (Tx.Ord a) => [(a, b)] -> Property
deletesAllPoly alist =
    let smap = SortedMap.fromListSafe alist
    in property $ SortedMap.null $ Tx.foldr (\(k,_) acc -> SortedMap.delete k acc) smap alist

membersAllPoly :: (Tx.Ord a) => [(a, b)] -> Property
membersAllPoly alist =
    let smap = SortedMap.fromListSafe alist
    in property $ Tx.and $ Tx.map ((`SortedMap.member` smap) . fst) alist

-- need to monomorphize to test with QC
prop_equivSortsNoDupl, prop_insertionSortFixesValidity, prop_mergeSortPreservesDuplicates, prop_deletesAll, prop_membersAll :: [(Integer, Integer)] -> Property

prop_equivSortsNoDupl = equivSortsNoDuplPoly
prop_insertionSortFixesValidity = insertionSortFixesValidityPoly
prop_mergeSortPreservesDuplicates = mergeSortPreservesDuplicatesPoly
prop_deletesAll = deletesAllPoly
prop_membersAll = membersAllPoly

propertyTests :: TestTree
propertyTests =
    testGroup "SortedMap"
        [ testProperty "merge-sort is equiv to insertion-sort for non-duplicated maps" prop_equivSortsNoDupl
        , testProperty "insertion-sort turns an invalid assocmap to a valid one" prop_insertionSortFixesValidity
        , testProperty "merge-sort preserves the (in)validity" prop_mergeSortPreservesDuplicates
        , testProperty "folding delete over all elements should make the Map empty" prop_deletesAll
        , testProperty "folding member over all elements succeeds" prop_membersAll
        ]
