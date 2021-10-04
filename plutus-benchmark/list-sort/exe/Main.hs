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
import           Control.Monad                            ()
import           Control.Monad.Trans.Except
import           Prelude                                  (div)
import           System.IO
import           Text.Printf                              (printf)

import           PlutusCore                               (Name (..))
import qualified PlutusCore                               as PLC
import           PlutusCore.Default
-- import qualified PlutusCore.Pretty                        as PLC
import           PlutusCore.Evaluation.Machine.ExBudget   (ExBudget (..))
import           PlutusCore.Evaluation.Machine.ExMemory   (ExCPU (..))
import qualified PlutusTx                                 as Tx
import           PlutusTx.Prelude                         as Tx
import qualified UntypedPlutusCore                        as UPLC
import           UntypedPlutusCore.Evaluation.Machine.Cek as Cek


-- Insertion sort

{-# INLINABLE isort #-}
isort :: [Integer] -> [Integer]
isort l0 = sort l0 []
    where sort [] r     = r
          sort (n:ns) r = sort ns (insert n r)
          insert n l =
              case l of
                [] -> [n]
                m:ms -> if n <= m
                        then n:l
                        else m:(insert n ms)

isortPlc :: Tx.CompiledCodeIn DefaultUni DefaultFun ([Integer] -> [Integer])
isortPlc = $$(Tx.compile [|| isort ||])

-- Quicksort

{-# INLINABLE qsort #-}
qsort :: [Integer] -> [Integer]
qsort []     = []
qsort (n:ns) = (qsort $ lt n ns []) ++ [n] ++ (qsort $ ge n ns [])
    where  lt _ [] r = r  -- Elements < x
           lt x (y:ys) r = if y < x
                         then lt x ys (y:r)
                         else lt x ys r
           ge _ [] r = r
           ge x (y:ys) r = if y >= x  -- Elements >= x
                         then ge x ys (y:r)
                         else ge x ys r

qsortPlc :: Tx.CompiledCodeIn DefaultUni DefaultFun ([Integer] -> [Integer])
qsortPlc = $$(Tx.compile [|| qsort ||])


{-# INLINABLE drop #-}
drop :: Integer -> [a] -> [a]
drop _ [] = []
drop n l@(_:xs) =
    if n <= 0 then l
    else drop (n-1) xs

{-# INLINABLE mergeList #-}
mergeList :: [Integer] -> [Integer] -> [Integer]
mergeList [] ys = ys
mergeList xs [] = xs
mergeList xs1@(x:xs) ys1@(y:ys) =
    if x <= y
    then x:(mergeList xs ys1)
    else y:(mergeList xs1 ys)

{-# INLINABLE mergeSort #-}
mergeSort :: [Integer] -> [Integer]
mergeSort xs =
    if n <= 1 then xs
    else
        mergeList
        (mergeSort (take (n `divide` 2) xs))
        (mergeSort (drop (n `divide` 2) xs))
        where
          n = length xs

msortPlc :: Tx.CompiledCodeIn DefaultUni DefaultFun ([Integer] -> [Integer])
msortPlc = $$(Tx.compile [|| mergeSort ||])


getUnDBrTerm
    :: UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
    -> UPLC.Term Name DefaultUni DefaultFun ()
getUnDBrTerm term =
    case runExcept @UPLC.FreeVariableError . PLC.runQuoteT . UPLC.unDeBruijnTerm $ term of
      Left e  -> throw e
      Right t -> t

evaluateWithCek
    :: UPLC.Term Name DefaultUni DefaultFun ()
    -> ( Either (CekEvaluationException DefaultUni DefaultFun)
                (UPLC.Term Name DefaultUni DefaultFun ())
       , CountingSt)
evaluateWithCek = runCekNoEmit PLC.defaultCekParameters Cek.counting

runSort :: Tx.CompiledCodeIn DefaultUni DefaultFun ([Integer] -> [Integer]) -> [Integer] -> IO ()
runSort sort l =
    let UPLC.Program _ _ code  = Tx.getPlc $ sort `Tx.applyCode` Tx.liftCode l
    in case evaluateWithCek $ getUnDBrTerm code of
         (Left _, _)  -> putStrLn "Error"
         (Right _, CountingSt c) ->
             let ExCPU cpu = exBudgetCPU c
             in putStr $ printf "%-4d %s\n" (length l) (PLC.show $ cpu`div` 1000000)

main :: IO ()
main =
    let l1 = [1000,999..1] :: [Integer]
        l2 = [1..1000] :: [Integer]
        l3 = [1..] :: [Integer]
        l = l3
        doSort sort = mapM_ (\n -> runSort sort (take n l)) [100,200..1000]
    in do
      putStrLn "Mergesort"
      putStrLn "---------"
      doSort msortPlc
      putStrLn "\n"
      putStrLn "Insertion sort"
      putStrLn "--------------"
      doSort isortPlc
      putStrLn "\n"
      putStrLn "Quicksort"
      putStrLn "---------"
      doSort qsortPlc
