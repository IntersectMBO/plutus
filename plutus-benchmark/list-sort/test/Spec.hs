{- | Tests for the Plutus nofib benchmarks, mostly comparing the result of Plutus
evaluation with the result of Haskell evaluation. Lastpiece is currently omitted
because its memory consumption as a Plutus program is too great to allow it to
run to completion. -}

module Main where

import           Test.Tasty
import           Test.Tasty.QuickCheck

import           PlutusBenchmark.Common                 (NamedDeBruijnTerm, cekResultMatchesHaskellValue)

import           PlutusBenchmark.ListSort.GhcSort
import           PlutusBenchmark.ListSort.InsertionSort
import           PlutusBenchmark.ListSort.MergeSort
import           PlutusBenchmark.ListSort.QuickSort

isSorted :: Ord a => [a] -> Bool
isSorted []       = True
isSorted [_]      = True
isSorted (a:b:cs) = a <= b && isSorted (b:cs)

-- | Check that a Haskell implementation of a sorting function really does sort
-- its input
prop_HaskellOK :: ([Integer] -> [Integer]) -> [Integer] -> Bool
prop_HaskellOK sort l = isSorted (sort l)

-- | Check that the Plutus translation of a Haskell sorting function gives the
-- same result as the Haskell version.
prop_PlutusOK :: ([Integer] -> [Integer]) -> ([Integer] -> NamedDeBruijnTerm) -> [Integer] -> Property
prop_PlutusOK sort termMaker l = cekResultMatchesHaskellValue (termMaker l) (===) (sort l)

---------------- Main ----------------

allTests :: TestTree
allTests =
  testGroup "plutus list-sort tests"
    [ testProperty "GHC sort (Haskell)"       $ prop_HaskellOK ghcSort
    , testProperty "GHC sort (Plutus)"        $ prop_PlutusOK  ghcSort mkGhcSortTerm
    , testProperty "insertion sort (Haskell)" $ prop_HaskellOK insertionSort
    , testProperty "insertion sort (Plutus)"  $ prop_PlutusOK  insertionSort mkInsertionSortTerm
    , testProperty "merge sort (Haskell)"     $ prop_HaskellOK mergeSort
    , testProperty "merge sort (Plutus)"      $ prop_PlutusOK  mergeSort mkMergeSortTerm
    , testProperty "quicksort (Haskell)"      $ prop_HaskellOK quickSort
    , testProperty "quicksort (Plutus)"       $ prop_PlutusOK  quickSort mkQuickSortTerm
    ]

main :: IO ()
main = defaultMain allTests
