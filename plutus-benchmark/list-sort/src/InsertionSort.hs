{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}

{-# OPTIONS_GHC -fno-warn-identities              #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds      #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns     #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module InsertionSort where

import           PlutusCore.Default
import qualified PlutusTx           as Tx
import           PlutusTx.Prelude   as Tx
import qualified UntypedPlutusCore  as UPLC


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

mkInsertionSortTerm :: [Integer] -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkInsertionSortTerm l =
    let (UPLC.Program _ _ code) = Tx.getPlc $ $$(Tx.compile [|| insertionSort ||]) `Tx.applyCode` Tx.liftCode l
    in code

mkWorstCaseInsertionSortTerm :: Integer -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
mkWorstCaseInsertionSortTerm = mkInsertionSortTerm . insertionSortWorstCase
