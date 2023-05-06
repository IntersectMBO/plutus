{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -fforce-recomp #-}
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
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests = testNested "Budget" [
    goldenBudget "sum" compiledSum
  , goldenUPlc "sum" compiledSum
  , goldenPirReadable "sum" compiledSum

  , goldenBudget "anyCheap" compiledAnyCheap
  , goldenUPlc "anyCheap" compiledAnyCheap
  , goldenPirReadable "anyCheap" compiledAnyCheap

  , goldenBudget "anyExpensive" compiledAnyExpensive
  , goldenUPlc "anyExpensive" compiledAnyExpensive
  , goldenPirReadable "anyExpensive" compiledAnyExpensive

  , goldenBudget "anyEmptyList" compiledAnyEmptyList
  , goldenUPlc "anyEmptyList" compiledAnyEmptyList
  , goldenPirReadable "anyEmptyList" compiledAnyEmptyList

  , goldenBudget "allCheap" compiledAllCheap
  , goldenUPlc "allCheap" compiledAllCheap
  , goldenPirReadable "allCheap" compiledAllCheap

  , goldenBudget "allExpensive" compiledAllExpensive
  , goldenUPlc "allExpensive" compiledAllExpensive
  , goldenPirReadable "allExpensive" compiledAllExpensive

  , goldenBudget "allEmptyList" compiledAllEmptyList
  , goldenUPlc "allEmptyList" compiledAllEmptyList
  , goldenPirReadable "allEmptyList" compiledAllEmptyList

  , goldenBudget "findCheap" compiledFindCheap
  , goldenUPlc "findCheap" compiledFindCheap
  , goldenPirReadable "findCheap" compiledFindCheap

  , goldenBudget "findExpensive" compiledFindExpensive
  , goldenUPlc "findExpensive" compiledFindExpensive
  , goldenPirReadable "findExpensive" compiledFindExpensive

  , goldenBudget "findEmptyList" compiledFindEmptyList
  , goldenUPlc "findEmptyList" compiledFindEmptyList
  , goldenPirReadable "findEmptyList" compiledFindEmptyList

  , goldenBudget "findIndexCheap" compiledFindIndexCheap
  , goldenUPlc "findIndexCheap" compiledFindIndexCheap
  , goldenPirReadable "findIndexCheap" compiledFindIndexCheap

  , goldenBudget "findIndexExpensive" compiledFindIndexExpensive
  , goldenUPlc "findIndexExpensive" compiledFindIndexExpensive
  , goldenPirReadable "findIndexExpensive" compiledFindIndexExpensive

  , goldenBudget "findIndexEmptyList" compiledFindIndexEmptyList
  , goldenUPlc "findIndexEmptyList" compiledFindIndexEmptyList
  , goldenPirReadable "findIndexEmptyList" compiledFindIndexEmptyList

  , goldenBudget "filter" compiledFilter
  , goldenUPlc "filter" compiledFilter
  , goldenPirReadable "filter" compiledFilter

  , goldenBudget "andCheap" compiledAndCheap
  , goldenUPlc "andCheap" compiledAndCheap
  , goldenPirReadable "andCheap" compiledAndCheap

  , goldenBudget "andExpensive" compiledAndExpensive
  , goldenUPlc "andExpensive" compiledAndExpensive
  , goldenPirReadable "andExpensive" compiledAndExpensive

  , goldenBudget "orCheap" compiledOrCheap
  , goldenUPlc "orCheap" compiledOrCheap
  , goldenPirReadable "orCheap" compiledOrCheap

  , goldenBudget "orExpensive" compiledOrExpensive
  , goldenUPlc "orExpensive" compiledOrExpensive
  , goldenPirReadable "orExpensive" compiledOrExpensive

  , goldenBudget "elemCheap" compiledElemCheap
  , goldenUPlc "elemCheap" compiledElemCheap
  , goldenPirReadable "elemCheap" compiledElemCheap

  , goldenBudget "elemExpensive" compiledElemExpensive
  , goldenUPlc "elemExpensive" compiledElemExpensive
  , goldenPirReadable "elemExpensive" compiledElemExpensive

  , goldenBudget "notElemCheap" compiledNotElemCheap
  , goldenUPlc "notElemCheap" compiledNotElemCheap
  , goldenPirReadable "notElemCheap" compiledNotElemCheap

  , goldenBudget "notElemExpensive" compiledNotElemExpensive
  , goldenUPlc "notElemExpensive" compiledNotElemExpensive
  , goldenPirReadable "notElemExpensive" compiledNotElemExpensive

  , goldenBudget "null" compiledNull
  , goldenUPlc "null" compiledNull
  , goldenPirReadable "null" compiledNull

  , goldenBudget "toFromData" compiledToFromData
  , goldenUPlc "toFromData" compiledToFromData
  , goldenPirReadable "toFromData" compiledToFromData

  , goldenBudget "monadicDo" monadicDo
  , goldenUPlc "monadicDo" monadicDo
  , goldenPirReadable "monadicDo" monadicDo
  -- These should be a little cheaper than the previous one,
  -- less overhead from going via monadic functions
  , goldenBudget "applicative" applicative
  , goldenUPlc "applicative" applicative
  , goldenPirReadable "applicative" applicative
  , goldenBudget "patternMatch" patternMatch
  , goldenUPlc "patternMatch" patternMatch
  , goldenPirReadable "patternMatch" patternMatch
  , goldenBudget "show" compiledShow
  , goldenUPlc "show" compiledShow
  , goldenPirReadable "show" compiledShow
  -- These test cases are for testing the float-in pass.
  , goldenBudget "ifThenElse1" compiledIfThenElse1
  , goldenUPlc "ifThenElse1" compiledIfThenElse1
  , goldenPirReadable "ifThenElse1" compiledIfThenElse1
  , goldenBudget "ifThenElse2" compiledIfThenElse2
  , goldenUPlc "ifThenElse2" compiledIfThenElse2
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

-- | The first element in the list satisfies the predicate.
compiledFindIndexCheap :: CompiledCode (Maybe Integer)
compiledFindIndexCheap = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.findIndex (10 PlutusTx.>) ls ||])

-- | No element in the list satisfies the predicate.
compiledFindIndexExpensive :: CompiledCode (Maybe Integer)
compiledFindIndexExpensive = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.findIndex (1 PlutusTx.>) ls ||])

compiledFindIndexEmptyList :: CompiledCode (Maybe Integer)
compiledFindIndexEmptyList = $$(compile [||
      let ls = [] :: [Integer]
       in PlutusTx.findIndex (1 PlutusTx.>) ls ||])

compiledFilter :: CompiledCode [Integer]
compiledFilter = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.filter PlutusTx.even ls ||])

-- | The first element is False so @and@ should short-circuit immediately.
compiledAndCheap :: CompiledCode Bool
compiledAndCheap = $$(compile [||
      let ls = [False, True, True, True, True, True, True, True, True, True]
       in PlutusTx.and ls ||])

-- | All elements are True so @and@ cannot short-circuit.
compiledAndExpensive :: CompiledCode Bool
compiledAndExpensive = $$(compile [||
      let ls = [True, True, True, True, True, True, True, True, True, True]
       in PlutusTx.and ls ||])

-- | The first element is True so @or@ should short-circuit immediately.
compiledOrCheap :: CompiledCode Bool
compiledOrCheap = $$(compile [||
      let ls = [True, False, False, False, False, False, False, False, False, False]
       in PlutusTx.or ls ||])

-- | All elements are False so @or@ cannot short-circuit.
compiledOrExpensive :: CompiledCode Bool
compiledOrExpensive = $$(compile [||
      let ls = [False, False, False, False, False, False, False, False, False, False]
       in PlutusTx.or ls ||])

-- | @elem@ can short-circuit
compiledElemCheap :: CompiledCode Bool
compiledElemCheap = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.elem 1 ls ||])

-- | @elem@ cannot short-circuit
compiledElemExpensive :: CompiledCode Bool
compiledElemExpensive = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.elem 0 ls ||])

-- | @notElem@ can short-circuit
compiledNotElemCheap :: CompiledCode Bool
compiledNotElemCheap = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.notElem 1 ls ||])

-- | @notElem@ cannot short-circuit
compiledNotElemExpensive :: CompiledCode Bool
compiledNotElemExpensive = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.notElem 0 ls ||])

compiledNull :: CompiledCode Bool
compiledNull = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.null ls ||])

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
