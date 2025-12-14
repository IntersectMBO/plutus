module Sort.Spec (tests) where

import Test.Tasty
import Test.Tasty.QuickCheck

import PlutusBenchmark.Common (Term, cekResultMatchesHaskellValue)

import PlutusBenchmark.Lists.Sort qualified as Sort

isSorted :: Ord a => [a] -> Bool
isSorted [] = True
isSorted [_] = True
isSorted (a : b : cs) = a <= b && isSorted (b : cs)

{-| Check that a Haskell implementation of a sorting function really does sort
its input. -}
prop_HaskellOK :: ([Integer] -> [Integer]) -> [Integer] -> Bool
prop_HaskellOK sort l = isSorted (sort l)

{-| Check that the Plutus translation of a Haskell sorting function gives the
same result as the Haskell version. -}
prop_PlutusOK :: ([Integer] -> [Integer]) -> ([Integer] -> Term) -> [Integer] -> Property
prop_PlutusOK sort termMaker l = cekResultMatchesHaskellValue (termMaker l) (===) (sort l)

tests :: TestTree
tests =
  testGroup
    "plutus-benchmark list-sort tests"
    [ testProperty "GHC sort (Haskell)" $ prop_HaskellOK Sort.ghcSort
    , testProperty "GHC sort (Plutus)" $ prop_PlutusOK Sort.ghcSort Sort.mkGhcSortTerm
    , testProperty "insertion sort (Haskell)" $ prop_HaskellOK Sort.insertionSort
    , testProperty "insertion sort (Plutus)" $
        prop_PlutusOK Sort.insertionSort Sort.mkInsertionSortTerm
    , testProperty "merge sort (Haskell)" $ prop_HaskellOK Sort.mergeSort
    , testProperty "merge sort (Plutus)" $ prop_PlutusOK Sort.mergeSort Sort.mkMergeSortTerm
    , testProperty "quicksort (Haskell)" $ prop_HaskellOK Sort.quickSort
    , testProperty "quicksort (Plutus)" $ prop_PlutusOK Sort.quickSort Sort.mkQuickSortTerm
    ]
