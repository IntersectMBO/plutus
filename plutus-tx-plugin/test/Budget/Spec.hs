{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}

module Budget.Spec where

import Test.Tasty.Extras

import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import PlutusTx.Test (goldenBudget, goldenPirReadable)
import PlutusTx.TH (compile)

tests :: TestNested
tests = testNested "Budget" [
    goldenBudget "sum" compiledSum
  , goldenPirReadable "sum" compiledSum

  , goldenBudget "anyCheap" compiledAnyCheap
  , goldenPirReadable "anyCheap" compiledAnyCheap

  , goldenBudget "anyExpensive" compiledAnyExpensive
  , goldenPirReadable "anyExpensive" compiledAnyExpensive

  , goldenBudget "anyEmptyList" compiledAnyEmptyList
  , goldenPirReadable "anyEmptyList" compiledAnyEmptyList

  , goldenBudget "allCheap" compiledAllCheap
  , goldenPirReadable "allCheap" compiledAllCheap

  , goldenBudget "allExpensive" compiledAllExpensive
  , goldenPirReadable "allExpensive" compiledAllExpensive

  , goldenBudget "allEmptyList" compiledAllEmptyList
  , goldenPirReadable "allEmptyList" compiledAllEmptyList

  , goldenBudget "findCheap" compiledFindCheap
  , goldenPirReadable "findCheap" compiledFindCheap

  , goldenBudget "findExpensive" compiledFindExpensive
  , goldenPirReadable "findExpensive" compiledFindExpensive

  , goldenBudget "findEmptyList" compiledFindEmptyList
  , goldenPirReadable "findEmptyList" compiledFindEmptyList

  , goldenBudget "filter" compiledFilter
  , goldenPirReadable "filter" compiledFilter

  , goldenBudget "elem" compiledElem
  , goldenPirReadable "elem" compiledElem

  , goldenBudget "toFromData" compiledToFromData
  , goldenPirReadable "toFromData" compiledToFromData

  , goldenBudget "monadicDo" monadicDo
  , goldenPirReadable "monadicDo" monadicDo
  -- These should be a little cheaper than the previous one,
  -- less overhead from going via monadic functions
  , goldenBudget "applicative" applicative
  , goldenPirReadable "applicative" applicative
  , goldenBudget "patternMatch" patternMatch
  , goldenPirReadable "patternMatch" patternMatch
  , goldenBudget "show" compiledShow
  , goldenPirReadable "show" compiledShow
  -- These test cases are for testing the float-in pass.
  , goldenBudget "ifThenElse1" compiledIfThenElse1
  , goldenPirReadable "ifThenElse1" compiledIfThenElse1
  , goldenBudget "ifThenElse2" compiledIfThenElse2
  , goldenPirReadable "ifThenElse2" compiledIfThenElse2
  ]

compiledSum :: CompiledCode Integer
compiledSum = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.sum ls ||])

-- | The first element in the list satisfies the predicate.
compiledAnyCheap :: CompiledCode Bool
compiledAnyCheap = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.any (10 PlutusTx.>) ls ||])

-- | No element in the list satisfies the predicate.
compiledAnyExpensive :: CompiledCode Bool
compiledAnyExpensive = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.any (1 PlutusTx.>) ls ||])

compiledAnyEmptyList :: CompiledCode Bool
compiledAnyEmptyList = $$(compile [||
      let ls = [] :: [Integer]
       in PlutusTx.any (1 PlutusTx.>) ls ||])

-- | The first element in the list does not satisfy the predicate.
compiledAllCheap :: CompiledCode Bool
compiledAllCheap = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.all (1 PlutusTx.>) ls ||])

-- | All elements in the list satisfy the predicate.
compiledAllExpensive :: CompiledCode Bool
compiledAllExpensive = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.all (11 PlutusTx.>) ls ||])

compiledAllEmptyList :: CompiledCode Bool
compiledAllEmptyList = $$(compile [||
      let ls = [] :: [Integer]
       in PlutusTx.all (1 PlutusTx.>) ls ||])

-- | The first element in the list satisfies the predicate.
compiledFindCheap :: CompiledCode (Maybe Integer)
compiledFindCheap = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.find (10 PlutusTx.>) ls ||])

-- | No element in the list satisfies the predicate.
compiledFindExpensive :: CompiledCode (Maybe Integer)
compiledFindExpensive = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.find (1 PlutusTx.>) ls ||])

compiledFindEmptyList :: CompiledCode (Maybe Integer)
compiledFindEmptyList = $$(compile [||
      let ls = [] :: [Integer]
       in PlutusTx.find (1 PlutusTx.>) ls ||])

compiledFilter :: CompiledCode [Integer]
compiledFilter = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.filter PlutusTx.even ls ||])

compiledElem :: CompiledCode Bool
compiledElem = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.elem 0 ls ||])

compiledToFromData :: CompiledCode (Either Integer (Maybe (Bool, Integer, Bool)))
compiledToFromData = $$(compile [||
      let
       v :: Either Integer (Maybe (Bool, Integer, Bool))
       v = Right (Just (True, 1, False))
       d :: PlutusTx.BuiltinData
       d = PlutusTx.toBuiltinData v
      in PlutusTx.unsafeFromBuiltinData d ||])

doExample :: Maybe Integer -> Maybe Integer -> Maybe Integer
doExample x y = do
    x' <- x
    y' <- y
    PlutusTx.pure (x' PlutusTx.+ y')

applicativeExample :: Maybe Integer -> Maybe Integer -> Maybe Integer
applicativeExample x y = (PlutusTx.+) PlutusTx.<$> x PlutusTx.<*> y

patternMatchExample :: Maybe Integer -> Maybe Integer -> Maybe Integer
patternMatchExample x y = case x of
    Just x' -> case y of
        Just y' -> Just (x' PlutusTx.+ y')
        Nothing -> Nothing
    Nothing -> Nothing

{-
Since upgrading to GHC 9.2.4, the optimized PIR for this test case contains
an additional let-binding:

@
(let
  (nonrec)
  (termbind
    (strict)
  (vardecl ds (con integer))
  [ [ (builtin addInteger) x ] y ]
  )
  [ { Just (con integer) } ds ]
)
@

This is likely caused by the @$fApplicativeMaybe_$cpure@ in the CoreExpr. In GHC 8,
it is inlined into @Just@.
-}
monadicDo :: CompiledCode (Maybe Integer)
monadicDo = $$(compile [||
      let x = Just 1
          y = Just 2
       in doExample x y ||])

applicative :: CompiledCode (Maybe Integer)
applicative = $$(compile [||
      let x = Just 1
          y = Just 2
       in applicativeExample x y ||])

patternMatch :: CompiledCode (Maybe Integer)
patternMatch = $$(compile [||
      let x = Just 1
          y = Just 2
       in patternMatchExample x y ||])

showExample :: Integer -> Integer
showExample x =
    let !a = PlutusTx.trace (PlutusTx.show x) x
        !b = PlutusTx.trace "This is an example" a
        !c = PlutusTx.trace (PlutusTx.show (PlutusTx.encodeUtf8 "This is an example")) b
        !d = PlutusTx.trace (PlutusTx.show (PlutusTx.greaterThanInteger c 0)) c
        !e = PlutusTx.trace (PlutusTx.show [a, b, c, d]) d
        !f = PlutusTx.trace (PlutusTx.show (a, b, c, d, e)) e
     in f `PlutusTx.multiplyInteger` 2

compiledShow :: CompiledCode Integer
compiledShow = $$(compile [||
      let x = -1234567890
       in showExample x ||])

-- | In this example, the float-in pass cannot reduce the cost unless it allows
-- unconditionally floating into type abstractions. Both branches are
-- turned into type abstractions (because the `a + a` branch is not a value).
compiledIfThenElse1 :: CompiledCode Integer
compiledIfThenElse1 = $$(compile [||
    let a = 1 PlutusTx.+ 2
     in if 3 PlutusTx.< (4 :: Integer)
          then 5
          else a PlutusTx.+ a ||])

-- | In this example, the float-in pass cannot reduce the cost unless it allows
-- unconditionally floating into lambda abstractions. Both branches are
-- lambda abstractions.
compiledIfThenElse2 :: CompiledCode Integer
compiledIfThenElse2 = $$(compile [||
    let a = 1 PlutusTx.+ 2
     in ( if 3 PlutusTx.< (4 :: Integer)
            then \x -> x PlutusTx.+ 5
            else \x -> x PlutusTx.+ a PlutusTx.+ a
        )
            (6 PlutusTx.+ 7) ||])
