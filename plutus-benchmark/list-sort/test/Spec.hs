{- | Tests for the Plutus nofib benchmarks, mostly comparing the result of Plutus
evaluation with the result of Haskell evaluation. Lastpiece is currently omitted
because its memory consumption as a Plutus program is too great to allow it to
run to completion. -}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}

module Main where

import           Control.Exception
import           Control.Monad.Except
import           Test.Tasty
import           Test.Tasty.QuickCheck

import           InsertionSort
import           MergeSort
import           QuickSort

import qualified PlutusCore                               as PLC
import           PlutusCore.Default
import qualified PlutusTx                                 as Tx
import qualified UntypedPlutusCore                        as UPLC
import           UntypedPlutusCore.Evaluation.Machine.Cek as UPLC (EvaluationResult (..), unsafeEvaluateCekNoEmit)

---------------- Evaluation ----------------

type NamedDeBruijnTerm = UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
type NamedTerm = UPLC.Term PLC.Name DefaultUni DefaultFun ()

runCek :: NamedDeBruijnTerm -> EvaluationResult NamedTerm
runCek t = case runExcept @UPLC.FreeVariableError $ PLC.runQuoteT $ UPLC.unDeBruijnTerm t of
    Left e   -> throw e
    Right t' -> UPLC.unsafeEvaluateCekNoEmit PLC.defaultCekParameters t'

termOfHaskellValue :: Tx.Lift DefaultUni a => a -> NamedDeBruijnTerm
termOfHaskellValue v =
    case Tx.getPlc $ Tx.liftCode v of
      UPLC.Program _ _ term -> term

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
prop_PlutusOK sort termMaker l = (runCek $ termMaker l) === (runCek $ termOfHaskellValue (sort l))

---------------- Main ----------------

allTests :: TestTree
allTests =
  testGroup "plutus list-sort tests"
    [ testProperty "insertion sort (Haskell)" $ prop_HaskellOK insertionSort
    , testProperty "insertion sort (Plutus)"  $ prop_PlutusOK  insertionSort mkInsertionSortTerm
    , testProperty "mergesort (Haskell)"      $ prop_HaskellOK mergeSort
    , testProperty "merge sort (Plutus)"      $ prop_PlutusOK  mergeSort mkMergeSortTerm
    , testProperty "quicksort (Haskell)"      $ prop_HaskellOK quickSort
    , testProperty "quicksort (Plutus)"       $ prop_PlutusOK  quickSort mkQuickSortTerm
    ]

main :: IO ()
main = defaultMain allTests
