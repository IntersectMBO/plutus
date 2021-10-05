{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-warn-identities              #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds      #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns     #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Main where

import           Control.Exception
import           Control.Monad.Trans.Except
import           Prelude                                  (div)
import           System.IO
import           Text.Printf                              (printf)

import           PlutusCore                               (Name (..))
import qualified PlutusCore                               as PLC
import           PlutusCore.Default
import           PlutusCore.Evaluation.Machine.ExBudget   (ExBudget (..))
import           PlutusCore.Evaluation.Machine.ExMemory   (ExCPU (..))
import qualified PlutusTx                                 as Tx
import           PlutusTx.Prelude                         as Tx
import qualified UntypedPlutusCore                        as UPLC
import qualified UntypedPlutusCore.Evaluation.Machine.Cek as Cek


-- Insertion sort

{-# INLINABLE insertionSort #-}
insertionSort :: [Integer] -> [Integer]
insertionSort l0 = sort l0 []
    where sort [] r     = r
          sort (n:ns) r = sort ns (insert n r)
          insert n acc =
              case acc of
                [] -> [n]
                m:ms -> if n <= m
                        then n:acc
                        else m:(insert n ms)

{- The worst case should be when the list is already sorted, since then whenever
   we insert a new element in the accumulator it'll have to go at the very end. -}
insertionSortWorstCase :: Integer -> [Integer]
insertionSortWorstCase n = [1..n]

insertionSortPlc :: Tx.CompiledCodeIn DefaultUni DefaultFun ([Integer] -> [Integer])
insertionSortPlc = $$(Tx.compile [|| insertionSort ||])

mkInsertionSortTerm :: Integer -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkInsertionSortTerm n =
  let (UPLC.Program _ _ code) = Tx.getPlc $
                                $$(Tx.compile [|| insertionSort ||])
                                `Tx.applyCode` Tx.liftCode (insertionSortWorstCase n)
  in code

-- Quicksort

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

mkQuickSortTerm :: Integer -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkQuickSortTerm n =
    let (UPLC.Program _ _ code) = Tx.getPlc $
                                  $$(Tx.compile [|| quickSort ||])
                                  `Tx.applyCode` Tx.liftCode (quickSortWorstCase n)
    in code

-- Mergesort

{-# INLINABLE drop #-}
drop :: Integer -> [a] -> [a]
drop _ [] = []
drop n l@(_:xs) =
    if n <= 0 then l
    else drop (n-1) xs

{-# INLINABLE merge #-}
merge :: [Integer] -> [Integer] -> [Integer]
merge [] ys = ys
merge xs [] = xs
merge xs1@(x:xs) ys1@(y:ys) =
    if x <= y
    then x:(merge xs ys1)
    else y:(merge xs1 ys)

{-# INLINABLE mergeSort #-}
mergeSort :: [Integer] -> [Integer]
mergeSort xs =
    if n <= 1 then xs
    else merge (mergeSort (take n2 xs)) (mergeSort (drop n2 xs))
        where
          n = length xs
          n2 = n `divide` 2

{- I think this is approximately the worst case.  A lot of the work happens in
   merge and this should make sure that the maximal amount of interleaving is
   required there.  If we merge [1,2,3,4] and [5,6,7,8] then we get to the case
   merge [] [5,6,7,8] which can return immediately; this function at n=8 gives us
   [1,5,3,7,2,6,4,8], which leads to merge [1,3,5,7] [2,4,6,8], and we have to go
   all the way to 1:2:3:4:5:6:7:(merge [] [8]) to merge those. -}
msortWorstCase :: Integer -> [Integer]
msortWorstCase n = f [1..n]
    where f ls =
              let (left, right) = unzip2 ls [] []
              in case (left, right) of
                   ([],_) -> right
                   (_,[]) -> left
                   _      -> f left ++ f right
          unzip2 l lacc racc =
              case l of
                []         -> (reverse lacc, reverse racc)
                [a]        -> (reverse(a:lacc), reverse racc)
                (a:b:rest) -> unzip2 rest (a:lacc) (b:racc)

msortPlc :: Tx.CompiledCodeIn DefaultUni DefaultFun ([Integer] -> [Integer])
msortPlc = $$(Tx.compile [|| mergeSort ||])

mkMsortTerm :: Integer -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkMsortTerm n =
  let (UPLC.Program _ _ code) = Tx.getPlc $
                                $$(Tx.compile [|| mergeSort ||])
                                `Tx.applyCode` Tx.liftCode (msortWorstCase n)
  in code

getUnDBrTerm
    :: UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
    -> UPLC.Term Name DefaultUni DefaultFun ()
getUnDBrTerm term =
    case runExcept @UPLC.FreeVariableError . PLC.runQuoteT . UPLC.unDeBruijnTerm $ term of
      Left e  -> throw e
      Right t -> t

evaluateWithCek
    :: UPLC.Term Name DefaultUni DefaultFun ()
    -> ( Either (Cek.CekEvaluationException DefaultUni DefaultFun)
                (UPLC.Term Name DefaultUni DefaultFun ())
       , Cek.CountingSt)
evaluateWithCek = Cek.runCekNoEmit PLC.defaultCekParameters Cek.counting

runSort :: Integer -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun () -> IO ()
runSort n term =
    case evaluateWithCek $ getUnDBrTerm term  of
      (Left _, _)  -> putStrLn "Error"
      (Right _, Cek.CountingSt c) ->
          let ExCPU cpu = exBudgetCPU c
          in putStr $ printf "%-4d %s\n" n (PLC.show $ cpu`div` 1000000)

main :: IO ()
main = do
  let inputLengths = [100,200..1000]
  putStrLn "Mergesort"
  putStrLn "---------"
  mapM_ (\n -> runSort n $ mkMsortTerm n) inputLengths
  putStrLn "\n"
  putStrLn "Insertion sort"
  putStrLn "--------------"
  mapM_ (\n -> runSort n (mkInsertionSortTerm n)) inputLengths
  putStrLn "\n"
  putStrLn "Quicksort"
  putStrLn "---------"
  mapM_ (\n -> runSort n (mkQuickSortTerm n)) inputLengths


