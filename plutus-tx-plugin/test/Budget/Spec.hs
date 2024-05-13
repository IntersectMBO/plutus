-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}

{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}

module Budget.Spec where

import Test.Tasty.Extras

import Budget.WithGHCOptimisations qualified as WithGHCOptTest
import Budget.WithoutGHCOptimisations qualified as WithoutGHCOptTest
import PlutusTx.AsData qualified as AsData
import PlutusTx.Builtins qualified as PlutusTx hiding (null)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Code
import PlutusTx.IsData qualified as IsData
import PlutusTx.Lift (liftCodeDef, makeLift)
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

AsData.asData [d|
  data MaybeD a = JustD a | NothingD
  |]
makeLift ''MaybeD

tests :: TestNested
tests = testNestedGhc "Budget" [
    goldenBudget "sum" compiledSum
  , goldenUPlcReadable "sum" compiledSum
  , goldenPirReadable "sum" compiledSum
  , goldenEvalCekCatch "sum" [compiledSum]

  , goldenBudget "anyCheap" compiledAnyCheap
  , goldenUPlcReadable "anyCheap" compiledAnyCheap
  , goldenPirReadable "anyCheap" compiledAnyCheap
  , goldenEvalCekCatch "anyCheap" [compiledAnyCheap]

  , goldenBudget "anyExpensive" compiledAnyExpensive
  , goldenUPlcReadable "anyExpensive" compiledAnyExpensive
  , goldenPirReadable "anyExpensive" compiledAnyExpensive
  , goldenEvalCekCatch "anyExpensive" [compiledAnyExpensive]

  , goldenBudget "anyEmptyList" compiledAnyEmptyList
  , goldenUPlcReadable "anyEmptyList" compiledAnyEmptyList
  , goldenPirReadable "anyEmptyList" compiledAnyEmptyList
  , goldenEvalCekCatch "anyEmptyList" [compiledAnyEmptyList]

  , goldenBudget "allCheap" compiledAllCheap
  , goldenUPlcReadable "allCheap" compiledAllCheap
  , goldenPirReadable "allCheap" compiledAllCheap
  , goldenEvalCekCatch "allCheap" [compiledAllCheap]

  , goldenBudget "allExpensive" compiledAllExpensive
  , goldenUPlcReadable "allExpensive" compiledAllExpensive
  , goldenPirReadable "allExpensive" compiledAllExpensive
  , goldenEvalCekCatch "allExpensive" [compiledAllExpensive]

  , goldenBudget "allEmptyList" compiledAllEmptyList
  , goldenUPlcReadable "allEmptyList" compiledAllEmptyList
  , goldenPirReadable "allEmptyList" compiledAllEmptyList
  , goldenEvalCekCatch "allEmptyList" [compiledAllEmptyList]

  , goldenBudget "findCheap" compiledFindCheap
  , goldenUPlcReadable "findCheap" compiledFindCheap
  , goldenPirReadable "findCheap" compiledFindCheap
  , goldenEvalCekCatch "findCheap" [compiledFindCheap]

  , goldenBudget "findExpensive" compiledFindExpensive
  , goldenUPlcReadable "findExpensive" compiledFindExpensive
  , goldenPirReadable "findExpensive" compiledFindExpensive
  , goldenEvalCekCatch "findExpensive" [compiledFindExpensive]

  , goldenBudget "findEmptyList" compiledFindEmptyList
  , goldenUPlcReadable "findEmptyList" compiledFindEmptyList
  , goldenPirReadable "findEmptyList" compiledFindEmptyList
  , goldenEvalCekCatch "findEmptyList" [compiledFindEmptyList]

  , goldenBudget "findIndexCheap" compiledFindIndexCheap
  , goldenUPlcReadable "findIndexCheap" compiledFindIndexCheap
  , goldenPirReadable "findIndexCheap" compiledFindIndexCheap
  , goldenEvalCekCatch "findIndexCheap" [compiledFindIndexCheap]

  , goldenBudget "findIndexExpensive" compiledFindIndexExpensive
  , goldenUPlcReadable "findIndexExpensive" compiledFindIndexExpensive
  , goldenPirReadable "findIndexExpensive" compiledFindIndexExpensive
  , goldenEvalCekCatch "findIndexExpensive" [compiledFindIndexExpensive]

  , goldenBudget "findIndexEmptyList" compiledFindIndexEmptyList
  , goldenUPlcReadable "findIndexEmptyList" compiledFindIndexEmptyList
  , goldenPirReadable "findIndexEmptyList" compiledFindIndexEmptyList
  , goldenEvalCekCatch "findIndexEmptyList" [compiledFindIndexEmptyList]

  , goldenBudget "filter" compiledFilter
  , goldenUPlcReadable "filter" compiledFilter
  , goldenPirReadable "filter" compiledFilter
  , goldenEvalCekCatch "filter" [compiledFilter]

  , goldenBudget "andCheap" compiledAndCheap
  , goldenUPlcReadable "andCheap" compiledAndCheap
  , goldenPirReadable "andCheap" compiledAndCheap
  , goldenEvalCekCatch "andCheap" [compiledAndCheap]

  , goldenBudget "andExpensive" compiledAndExpensive
  , goldenUPlcReadable "andExpensive" compiledAndExpensive
  , goldenPirReadable "andExpensive" compiledAndExpensive
  , goldenEvalCekCatch "andExpensive" [compiledAndExpensive]

  , goldenBudget "orCheap" compiledOrCheap
  , goldenUPlcReadable "orCheap" compiledOrCheap
  , goldenPirReadable "orCheap" compiledOrCheap
  , goldenEvalCekCatch "orCheap" [compiledOrCheap]

  , goldenBudget "orExpensive" compiledOrExpensive
  , goldenUPlcReadable "orExpensive" compiledOrExpensive
  , goldenPirReadable "orExpensive" compiledOrExpensive
  , goldenEvalCekCatch "orExpensive" [compiledOrExpensive]

  , goldenBudget "elemCheap" compiledElemCheap
  , goldenUPlcReadable "elemCheap" compiledElemCheap
  , goldenPirReadable "elemCheap" compiledElemCheap
  , goldenEvalCekCatch "elemCheap" [compiledElemCheap]

  , goldenBudget "elemExpensive" compiledElemExpensive
  , goldenUPlcReadable "elemExpensive" compiledElemExpensive
  , goldenPirReadable "elemExpensive" compiledElemExpensive
  , goldenEvalCekCatch "elemExpensive" [compiledElemExpensive]

  , goldenBudget "notElemCheap" compiledNotElemCheap
  , goldenUPlcReadable "notElemCheap" compiledNotElemCheap
  , goldenPirReadable "notElemCheap" compiledNotElemCheap
  , goldenEvalCekCatch "notElemCheap" [compiledNotElemCheap]

  , goldenBudget "notElemExpensive" compiledNotElemExpensive
  , goldenUPlcReadable "notElemExpensive" compiledNotElemExpensive
  , goldenPirReadable "notElemExpensive" compiledNotElemExpensive
  , goldenEvalCekCatch "notElemExpensive" [compiledNotElemExpensive]

  , goldenBudget "lte0" compiledLte0
  , goldenUPlcReadable "lte0" compiledLte0
  , goldenPirReadable "lte0" compiledLte0
  , goldenEvalCekCatch "lte0" [compiledLte0]

  , goldenBudget "gte0" compiledGte0
  , goldenUPlcReadable "gte0" compiledGte0
  , goldenPirReadable "gte0" compiledGte0
  , goldenEvalCekCatch "gte0" [compiledGte0]

  , goldenBudget "recursiveLte0" compiledRecursiveLte0
  , goldenUPlcReadable "recursiveLte0" compiledRecursiveLte0
  , goldenPirReadable "recursiveLte0" compiledRecursiveLte0
  , goldenEvalCekCatch "recursiveLte0" [compiledRecursiveLte0]

  , goldenBudget "recursiveGte0" compiledRecursiveGte0
  , goldenUPlcReadable "recursiveGte0" compiledRecursiveGte0
  , goldenPirReadable "recursiveGte0" compiledRecursiveGte0
  , goldenEvalCekCatch "recursiveGte0" [compiledRecursiveGte0]

  , goldenBudget "sumL" compiledSumL
  , goldenUPlcReadable "sumL" compiledSumL
  , goldenPirReadable "sumL" compiledSumL
  , goldenEvalCekCatch "sumL" [compiledSumL]

  , goldenBudget "sumR" compiledSumR
  , goldenUPlcReadable "sumR" compiledSumR
  , goldenPirReadable "sumR" compiledSumR
  , goldenEvalCekCatch "sumR" [compiledSumR]

  , goldenBudget "constAccL" compiledConstAccL
  , goldenUPlcReadable "constAccL" compiledConstAccL
  , goldenPirReadable "constAccL" compiledConstAccL
  , goldenEvalCekCatch "constAccL" [compiledConstAccL]

  , goldenBudget "constAccR" compiledConstAccR
  , goldenUPlcReadable "constAccR" compiledConstAccR
  , goldenPirReadable "constAccR" compiledConstAccR
  , goldenEvalCekCatch "constAccR" [compiledConstAccR]

  , goldenBudget "constElL" compiledConstElL
  , goldenUPlcReadable "constElL" compiledConstElL
  , goldenPirReadable "constElL" compiledConstElL
  , goldenEvalCekCatch "constElL" [compiledConstElL]

  , goldenBudget "constElR" compiledConstElR
  , goldenUPlcReadable "constElR" compiledConstElR
  , goldenPirReadable "constElR" compiledConstElR
  , goldenEvalCekCatch "constElR" [compiledConstElR]

  , goldenBudget "null" compiledNull
  , goldenUPlcReadable "null" compiledNull
  , goldenPirReadable "null" compiledNull
  , goldenEvalCekCatch "null" [compiledNull]

  , goldenUPlcReadable "listIndexing" compiledListIndexing
  , goldenPirReadable "listIndexing" compiledListIndexing
  , goldenEvalCekCatch
      "listIndexing"
      [compiledListIndexing `unsafeApplyCode` liftCodeDef listIndexingInput]
  , goldenBudget
      "listIndexing"
      (compiledListIndexing `unsafeApplyCode` liftCodeDef listIndexingInput)

  , goldenUPlcReadable "builtinListIndexing" compiledBuiltinListIndexing
  , goldenPirReadable "builtinListIndexing" compiledBuiltinListIndexing
  , goldenEvalCekCatch
      "builtinListIndexing"
      [compiledBuiltinListIndexing `unsafeApplyCode` liftCodeDef builtinListIndexingInput]
  , goldenBudget
      "builtinListIndexing"
      (compiledBuiltinListIndexing `unsafeApplyCode` liftCodeDef builtinListIndexingInput)

  , goldenBudget "toFromData" compiledToFromData
  , goldenUPlcReadable "toFromData" compiledToFromData
  , goldenPirReadable "toFromData" compiledToFromData
  , goldenEvalCekCatch "toFromData" [compiledToFromData]

  , goldenBudget "not-not" compiledNotNot
  , goldenUPlcReadable "not-not" compiledNotNot
  , goldenPirReadable "not-not" compiledNotNot
  , goldenEvalCekCatch "not-not" [compiledNotNot]

  , goldenBudget "monadicDo" monadicDo
  , goldenUPlcReadable "monadicDo" monadicDo
  , goldenPirReadable "monadicDo" monadicDo
  , goldenEvalCekCatch "monadicDo" [monadicDo]

  -- These should be a little cheaper than the previous one,
  -- less overhead from going via monadic functions
  , goldenBudget "applicative" applicative
  , goldenUPlcReadable "applicative" applicative
  , goldenPirReadable "applicative" applicative
  , goldenEvalCekCatch "applicative" [applicative]

  , goldenBudget "patternMatch" patternMatch
  , goldenUPlcReadable "patternMatch" patternMatch
  , goldenPirReadable "patternMatch" patternMatch
  , goldenEvalCekCatch "patternMatch" [patternMatch]

  , goldenBudget "show" compiledShow
  , goldenUPlcReadable "show" compiledShow
  , goldenPirReadable "show" compiledShow

  -- These test cases are for testing the float-in pass.
  , goldenBudget "ifThenElse1" compiledIfThenElse1
  , goldenUPlcReadable "ifThenElse1" compiledIfThenElse1
  , goldenPirReadable "ifThenElse1" compiledIfThenElse1
  , goldenEvalCekCatch "ifThenElse1" [compiledIfThenElse1]

  , goldenBudget "ifThenElse2" compiledIfThenElse2
  , goldenUPlcReadable "ifThenElse2" compiledIfThenElse2
  , goldenPirReadable "ifThenElse2" compiledIfThenElse2
  , goldenEvalCekCatch "ifThenElse2" [compiledIfThenElse2]

  , goldenBudget "matchAsDataE" matchAsData
  , goldenEvalCekCatch "matchAsDataE" [matchAsData]

  -- Demonstrate inconsistent handling of '&&' and '||'
  -- With GHC optimisations turned on
  , goldenBudget "andWithGHCOpts" compiledAndWithGHCOpts
  , goldenUPlcReadable "andWithGHCOpts" compiledAndWithGHCOpts
  , goldenPirReadable "andWithGHCOpts" compiledAndWithGHCOpts
  , goldenEvalCekCatch "andWithGHCOpts" [compiledAndWithGHCOpts]
  -- With GHC optimisations turned off
  , goldenBudget "andWithoutGHCOpts" compiledAndWithoutGHCOpts
  , goldenUPlcReadable "andWithoutGHCOpts" compiledAndWithoutGHCOpts
  , goldenPirReadable "andWithoutGHCOpts" compiledAndWithoutGHCOpts
  , goldenEvalCekCatch "andWithoutGHCOpts" [compiledAndWithoutGHCOpts]
  -- With the function definition in the local module
  , goldenBudget "andWithLocal" compiledAndWithLocal
  , goldenUPlcReadable "andWithLocal" compiledAndWithLocal
  , goldenPirReadable "andWithLocal" compiledAndWithLocal
  , goldenEvalCekCatch "andWithLocal" [compiledAndWithLocal]
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

-- | Check @0 <= 0@ a thousand times using @all@ that inlines.
compiledLte0 :: CompiledCode Bool
compiledLte0 = $$(compile [||
      let ls = PlutusTx.replicate 1000 0 :: [Integer]
       in List.all (PlutusTx.<= 0) ls ||])

-- | Check @0 >= 0@ a thousand times using @all@ that inlines.
compiledGte0 :: CompiledCode Bool
compiledGte0 = $$(compile [||
      let ls = PlutusTx.replicate 1000 0 :: [Integer]
       in List.all (PlutusTx.>= 0) ls ||])

{-# INLINABLE recursiveAll #-}
-- | A version of @all@ that doesn't inline due to being recursive.
recursiveAll :: forall a. (a -> Bool) -> [a] -> Bool
recursiveAll _ []     = True
recursiveAll f (x:xs) = if f x then recursiveAll f xs else False

-- | Check @0 <= 0@ a thousand times using @all@ that doesn't inline.
compiledRecursiveLte0 :: CompiledCode Bool
compiledRecursiveLte0 = $$(compile [||
      let ls = PlutusTx.replicate 1000 0 :: [Integer]
       in recursiveAll (PlutusTx.<= 0) ls ||])

-- | Check @0 >= 0@ a thousand times using @all@ that doesn't inline.
compiledRecursiveGte0 :: CompiledCode Bool
compiledRecursiveGte0 = $$(compile [||
      let ls = PlutusTx.replicate 1000 0 :: [Integer]
       in recursiveAll (PlutusTx.>= 0) ls ||])

-- | Left-fold a list with a function summing its arguments.
compiledSumL :: CompiledCode Integer
compiledSumL = $$(compile [||
      let ls = PlutusTx.enumFromTo 1 1000 :: [Integer]
       in List.foldl (PlutusTx.+) 0 ls ||])

-- | Right-fold a list with a function summing its arguments.
compiledSumR :: CompiledCode Integer
compiledSumR = $$(compile [||
      let ls = PlutusTx.enumFromTo 1 1000 :: [Integer]
       in List.foldr (PlutusTx.+) 0 ls ||])

-- | Left-fold a list with a function returning the accumulator.
compiledConstAccL :: CompiledCode Integer
compiledConstAccL = $$(compile [||
      let ls = PlutusTx.replicate 1000 (1 :: Integer)
       in List.foldl (\acc _ -> acc) 42 ls ||])

-- | Right-fold a list with a function returning the accumulator.
compiledConstAccR :: CompiledCode Integer
compiledConstAccR = $$(compile [||
      let ls = PlutusTx.replicate 1000 (1 :: Integer)
       in List.foldr (\_ acc -> acc) 42 ls ||])

-- | Left-fold a list with a function returning a list element, the result is the last element.
compiledConstElL :: CompiledCode Integer
compiledConstElL = $$(compile [||
      let ls = PlutusTx.replicate 1000 (1 :: Integer)
       in List.foldl (\_ el -> el) 42 ls ||])

-- | Right-fold a list with a function returning a list element, the result is the first element.
compiledConstElR :: CompiledCode Integer
compiledConstElR = $$(compile [||
      let ls = PlutusTx.replicate 1000 (1 :: Integer)
       in List.foldr (\el _ -> el) 42 ls ||])

compiledNull :: CompiledCode Bool
compiledNull = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.null ls ||])

compiledListIndexing :: CompiledCode ([PlutusTx.BuiltinData] -> PlutusTx.BuiltinData)
compiledListIndexing = $$(compile [||
      \xs -> xs List.!! 5 ||])

compiledBuiltinListIndexing :: CompiledCode (PlutusTx.BuiltinData -> PlutusTx.BuiltinData)
compiledBuiltinListIndexing = $$(compile [||
      \d -> BI.unsafeDataAsList d `List.indexBuiltinList` 5 ||])

listIndexingInput :: [PlutusTx.BuiltinData]
listIndexingInput = IsData.toBuiltinData <$> [1 :: Integer .. 10]

builtinListIndexingInput :: PlutusTx.BuiltinData
builtinListIndexingInput = IsData.toBuiltinData listIndexingInput

compiledToFromData :: CompiledCode (Either Integer (Maybe (Bool, Integer, Bool)))
compiledToFromData = $$(compile [||
      let
       v :: Either Integer (Maybe (Bool, Integer, Bool))
       v = Right (Just (True, 1, False))
       d :: PlutusTx.BuiltinData
       d = IsData.toBuiltinData v
      in IsData.unsafeFromBuiltinData d ||])

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

-- TODO: this can be further optimized.
compiledNotNot :: CompiledCode Bool
compiledNotNot =
  $$( compile
        [||
        \x ->
          (\a -> if a then False else True) . (\a -> if a then False else True) PlutusTx.$
            if PlutusTx.lessThanInteger 0 x then True else False
        ||]
    )
    `PlutusTx.Code.unsafeApplyCode` liftCodeDef 1

matchAsData :: CompiledCode Integer
matchAsData = $$(compile [||
  \case
    JustD a  -> a
    NothingD -> 1 ||])
    `PlutusTx.Code.unsafeApplyCode` liftCodeDef (JustD 1)

compiledAndWithGHCOpts :: CompiledCode Bool
compiledAndWithGHCOpts =
  let code = $$(compile [|| WithGHCOptTest.f ||])
   in flip PlutusTx.Code.unsafeApplyCode (liftCodeDef (4 :: Integer)) $
        PlutusTx.Code.unsafeApplyCode code (liftCodeDef (4 :: Integer))

compiledAndWithoutGHCOpts :: CompiledCode Bool
compiledAndWithoutGHCOpts =
  let code = $$(compile [|| WithoutGHCOptTest.f ||])
   in flip PlutusTx.Code.unsafeApplyCode (liftCodeDef (4 :: Integer)) $
        PlutusTx.Code.unsafeApplyCode code (liftCodeDef (4 :: Integer))

compiledAndWithLocal :: CompiledCode Bool
compiledAndWithLocal =
  let f :: Integer -> Integer -> Bool
      f x y = (PlutusTx.&&) (x PlutusTx.< (3 :: Integer)) (y PlutusTx.< (3 :: Integer))
      code = $$(compile [|| f ||])
   in flip PlutusTx.Code.unsafeApplyCode (liftCodeDef (4 :: Integer)) $
        PlutusTx.Code.unsafeApplyCode code (liftCodeDef (4 :: Integer))
