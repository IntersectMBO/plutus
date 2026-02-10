-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Redundant if" #-}

module Budget.Spec where

import Test.Tasty.Extras

import Budget.BuiltinAndLib qualified as BuiltinAndLib
import Budget.WithGHCOptimisations qualified as WithGHCOptTest
import Budget.WithoutGHCOptimisations qualified as WithoutGHCOptTest
import Data.Set qualified as Set
import PlutusTx.AsData qualified as AsData
import PlutusTx.Builtins qualified as PlutusTx hiding (null)
import PlutusTx.Code
import PlutusTx.Data.List (List)
import PlutusTx.Data.List.TH (destructList)
import PlutusTx.Foldable qualified as F
import PlutusTx.IsData qualified as IsData
import PlutusTx.Lift (liftCodeDef, makeLift)
import PlutusTx.List qualified as List
import PlutusTx.Prelude
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import PlutusTx.TH (compile)
import PlutusTx.Test

AsData.asData [d|data MaybeD a = JustD a | NothingD|]
makeLift ''MaybeD

tests :: TestNested
tests =
  testNested "Budget"
    . pure
    $ testNestedGhc
      [ goldenBundle' "sum" compiledSum
      , goldenBundle' "anyCheap" compiledAnyCheap
      , goldenBundle' "anyExpensive" compiledAnyExpensive
      , goldenBundle' "anyEmptyList" compiledAnyEmptyList
      , goldenBundle' "allCheap" compiledAllCheap
      , goldenBundle' "allExpensive" compiledAllExpensive
      , goldenBundle' "allEmptyList" compiledAllEmptyList
      , goldenBundle' "findCheap" compiledFindCheap
      , goldenBundle' "findExpensive" compiledFindExpensive
      , goldenBundle' "findEmptyList" compiledFindEmptyList
      , goldenBundle' "findIndexCheap" compiledFindIndexCheap
      , goldenBundle' "findIndexExpensive" compiledFindIndexExpensive
      , goldenBundle' "findIndexEmptyList" compiledFindIndexEmptyList
      , goldenBundle' "filter" compiledFilter
      , goldenBundle' "andCheap" compiledAndCheap
      , goldenBundle' "andExpensive" compiledAndExpensive
      , goldenBundle' "orCheap" compiledOrCheap
      , goldenBundle' "orExpensive" compiledOrExpensive
      , goldenBundle' "elemCheap" compiledElemCheap
      , goldenBundle' "elemExpensive" compiledElemExpensive
      , goldenBundle' "notElemCheap" compiledNotElemCheap
      , goldenBundle' "notElemExpensive" compiledNotElemExpensive
      , goldenBundle' "lte0" compiledLte0
      , goldenBundle' "gte0" compiledGte0
      , goldenBundle' "recursiveLte0" compiledRecursiveLte0
      , goldenBundle' "recursiveGte0" compiledRecursiveGte0
      , goldenBundle' "sumL" compiledSumL
      , goldenBundle' "sumR" compiledSumR
      , goldenBundle' "constAccL" compiledConstAccL
      , goldenBundle' "constAccR" compiledConstAccR
      , goldenBundle' "constElL" compiledConstElL
      , goldenBundle' "constElR" compiledConstElR
      , goldenBundle' "null" compiledNull
      , goldenBundle
          "listIndexing"
          compiledListIndexing
          (compiledListIndexing `unsafeApplyCode` liftCodeDef listIndexingInput)
      , goldenBundle' "toFromData" compiledToFromData
      , goldenBundle' "not-not" compiledNotNot
      , goldenBundle' "monadicDo" monadicDo
      , goldenBundle
          "sumAtIndices"
          compiledSumAtIndices
          (compiledSumAtIndices `unsafeApplyCode` sumAtIndicesInput)
      , -- These should be a little cheaper than the previous one,
        -- less overhead from going via monadic functions
        goldenBundle' "applicative" applicative
      , goldenBundle' "patternMatch" patternMatch
      , goldenBundle' "show" compiledShow
      , -- These test cases are for testing the float-in pass.
        goldenBundle' "ifThenElse1" compiledIfThenElse1
      , goldenBundle' "ifThenElse2" compiledIfThenElse2
      , goldenBundle' "matchAsDataE" matchAsData
      , -- Demonstrate inconsistent handling of '&&' and '||'
        -- With GHC optimisations turned on
        goldenBundle' "andWithGHCOpts" compiledAndWithGHCOpts
      , -- With GHC optimisations turned off
        goldenBundle' "andWithoutGHCOpts" compiledAndWithoutGHCOpts
      , -- With the function definition in the local module
        goldenBundle' "andWithLocal" compiledAndWithLocal
      , -- && vs builtinAnd vs alternatives: boolean AND chaining budget
        -- Pattern 1: Standard && (lazy, delay/force)
        goldenBundle' "andLazy_AllTrue" andLazy_AllTrue
      , goldenBundle' "andLazy_EarlyFail" andLazy_EarlyFail
      , goldenBundle' "andLazy_LateFail" andLazy_LateFail
      , -- Pattern 2: builtinAnd (lambda/unit)
        goldenBundle' "andBuiltinAnd_AllTrue" andBuiltinAnd_AllTrue
      , goldenBundle' "andBuiltinAnd_EarlyFail" andBuiltinAnd_EarlyFail
      , goldenBundle' "andBuiltinAnd_LateFail" andBuiltinAnd_LateFail
      , -- Pattern 3: Multi-way if (negated guards)
        goldenBundle' "andMultiWayIf_AllTrue" andMultiWayIf_AllTrue
      , goldenBundle' "andMultiWayIf_EarlyFail" andMultiWayIf_EarlyFail
      , goldenBundle' "andMultiWayIf_LateFail" andMultiWayIf_LateFail
      , -- Pattern 4: Direct BI.ifThenElse chain (manual lambda/unit)
        goldenBundle' "andDirectIfThenElse_AllTrue" andDirectIfThenElse_AllTrue
      , goldenBundle' "andDirectIfThenElse_EarlyFail" andDirectIfThenElse_EarlyFail
      , goldenBundle' "andDirectIfThenElse_LateFail" andDirectIfThenElse_LateFail
      ]

compiledSum :: CompiledCode Integer
compiledSum =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in F.sum ls
        ||]
    )

-- | The first element in the list satisfies the predicate.
compiledAnyCheap :: CompiledCode Bool
compiledAnyCheap =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.any (10 PlutusTx.>) ls
        ||]
    )

-- | No element in the list satisfies the predicate.
compiledAnyExpensive :: CompiledCode Bool
compiledAnyExpensive =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.any (1 PlutusTx.>) ls
        ||]
    )

compiledAnyEmptyList :: CompiledCode Bool
compiledAnyEmptyList =
  $$( compile
        [||
        let ls = [] :: [Integer]
         in List.any (1 PlutusTx.>) ls
        ||]
    )

-- | The first element in the list does not satisfy the predicate.
compiledAllCheap :: CompiledCode Bool
compiledAllCheap =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.all (1 PlutusTx.>) ls
        ||]
    )

-- | All elements in the list satisfy the predicate.
compiledAllExpensive :: CompiledCode Bool
compiledAllExpensive =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.all (11 PlutusTx.>) ls
        ||]
    )

compiledAllEmptyList :: CompiledCode Bool
compiledAllEmptyList =
  $$( compile
        [||
        let ls = [] :: [Integer]
         in List.all (1 PlutusTx.>) ls
        ||]
    )

-- | The first element in the list satisfies the predicate.
compiledFindCheap :: CompiledCode (Maybe Integer)
compiledFindCheap =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.find (10 PlutusTx.>) ls
        ||]
    )

-- | No element in the list satisfies the predicate.
compiledFindExpensive :: CompiledCode (Maybe Integer)
compiledFindExpensive =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.find (1 PlutusTx.>) ls
        ||]
    )

compiledFindEmptyList :: CompiledCode (Maybe Integer)
compiledFindEmptyList =
  $$( compile
        [||
        let ls = [] :: [Integer]
         in List.find (1 PlutusTx.>) ls
        ||]
    )

-- | The first element in the list satisfies the predicate.
compiledFindIndexCheap :: CompiledCode (Maybe Integer)
compiledFindIndexCheap =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.findIndex (10 PlutusTx.>) ls
        ||]
    )

-- | No element in the list satisfies the predicate.
compiledFindIndexExpensive :: CompiledCode (Maybe Integer)
compiledFindIndexExpensive =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.findIndex (1 PlutusTx.>) ls
        ||]
    )

compiledFindIndexEmptyList :: CompiledCode (Maybe Integer)
compiledFindIndexEmptyList =
  $$( compile
        [||
        let ls = [] :: [Integer]
         in List.findIndex (1 PlutusTx.>) ls
        ||]
    )

compiledFilter :: CompiledCode [Integer]
compiledFilter =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.filter PlutusTx.even ls
        ||]
    )

-- | The first element is False so @and@ should short-circuit immediately.
compiledAndCheap :: CompiledCode Bool
compiledAndCheap =
  $$( compile
        [||
        let ls = [False, True, True, True, True, True, True, True, True, True]
         in List.and ls
        ||]
    )

-- | All elements are True so @and@ cannot short-circuit.
compiledAndExpensive :: CompiledCode Bool
compiledAndExpensive =
  $$( compile
        [||
        let ls = [True, True, True, True, True, True, True, True, True, True]
         in List.and ls
        ||]
    )

-- | The first element is True so @or@ should short-circuit immediately.
compiledOrCheap :: CompiledCode Bool
compiledOrCheap =
  $$( compile
        [||
        let ls = [True, False, False, False, False, False, False, False, False, False]
         in List.or ls
        ||]
    )

-- | All elements are False so @or@ cannot short-circuit.
compiledOrExpensive :: CompiledCode Bool
compiledOrExpensive =
  $$( compile
        [||
        let ls = [False, False, False, False, False, False, False, False, False, False]
         in List.or ls
        ||]
    )

-- | @elem@ can short-circuit
compiledElemCheap :: CompiledCode Bool
compiledElemCheap =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.elem 1 ls
        ||]
    )

-- | @elem@ cannot short-circuit
compiledElemExpensive :: CompiledCode Bool
compiledElemExpensive =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.elem 0 ls
        ||]
    )

-- | @notElem@ can short-circuit
compiledNotElemCheap :: CompiledCode Bool
compiledNotElemCheap =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.notElem 1 ls
        ||]
    )

-- | @notElem@ cannot short-circuit
compiledNotElemExpensive :: CompiledCode Bool
compiledNotElemExpensive =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.notElem 0 ls
        ||]
    )

-- | Check @0 <= 0@ a thousand times using @all@ that inlines.
compiledLte0 :: CompiledCode Bool
compiledLte0 =
  $$( compile
        [||
        let ls = List.replicate 1000 0 :: [Integer]
         in List.all (PlutusTx.<= 0) ls
        ||]
    )

-- | Check @0 >= 0@ a thousand times using @all@ that inlines.
compiledGte0 :: CompiledCode Bool
compiledGte0 =
  $$( compile
        [||
        let ls = List.replicate 1000 0 :: [Integer]
         in List.all (PlutusTx.>= 0) ls
        ||]
    )

-- | A version of @all@ that doesn't inline due to being recursive.
recursiveAll :: forall a. (a -> Bool) -> [a] -> Bool
recursiveAll _ [] = True
recursiveAll f (x : xs) = if f x then recursiveAll f xs else False
{-# INLINEABLE recursiveAll #-}

-- | Check @0 <= 0@ a thousand times using @all@ that doesn't inline.
compiledRecursiveLte0 :: CompiledCode Bool
compiledRecursiveLte0 =
  $$( compile
        [||
        let ls = List.replicate 1000 0 :: [Integer]
         in recursiveAll (PlutusTx.<= 0) ls
        ||]
    )

-- | Check @0 >= 0@ a thousand times using @all@ that doesn't inline.
compiledRecursiveGte0 :: CompiledCode Bool
compiledRecursiveGte0 =
  $$( compile
        [||
        let ls = List.replicate 1000 0 :: [Integer]
         in recursiveAll (PlutusTx.>= 0) ls
        ||]
    )

-- | Left-fold a list with a function summing its arguments.
compiledSumL :: CompiledCode Integer
compiledSumL =
  $$( compile
        [||
        let ls = PlutusTx.enumFromTo 1 1000 :: [Integer]
         in List.foldl (PlutusTx.+) 0 ls
        ||]
    )

-- | Right-fold a list with a function summing its arguments.
compiledSumR :: CompiledCode Integer
compiledSumR =
  $$( compile
        [||
        let ls = PlutusTx.enumFromTo 1 1000 :: [Integer]
         in List.foldr (PlutusTx.+) 0 ls
        ||]
    )

-- | Left-fold a list with a function returning the accumulator.
compiledConstAccL :: CompiledCode Integer
compiledConstAccL =
  $$( compile
        [||
        let ls = List.replicate 1000 (1 :: Integer)
         in List.foldl (\acc _ -> acc) 42 ls
        ||]
    )

-- | Right-fold a list with a function returning the accumulator.
compiledConstAccR :: CompiledCode Integer
compiledConstAccR =
  $$( compile
        [||
        let ls = List.replicate 1000 (1 :: Integer)
         in List.foldr (\_ acc -> acc) 42 ls
        ||]
    )

-- | Left-fold a list with a function returning a list element, the result is the last element.
compiledConstElL :: CompiledCode Integer
compiledConstElL =
  $$( compile
        [||
        let ls = List.replicate 1000 (1 :: Integer)
         in List.foldl (\_ el -> el) 42 ls
        ||]
    )

-- | Right-fold a list with a function returning a list element, the result is the first element.
compiledConstElR :: CompiledCode Integer
compiledConstElR =
  $$( compile
        [||
        let ls = List.replicate 1000 (1 :: Integer)
         in List.foldr (\el _ -> el) 42 ls
        ||]
    )

compiledNull :: CompiledCode Bool
compiledNull =
  $$( compile
        [||
        let ls = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Integer]
         in List.null ls
        ||]
    )

compiledListIndexing :: CompiledCode ([PlutusTx.BuiltinData] -> PlutusTx.BuiltinData)
compiledListIndexing =
  $$( compile
        [||
        \xs -> xs List.!! 5
        ||]
    )

listIndexingInput :: [PlutusTx.BuiltinData]
listIndexingInput = IsData.toBuiltinData <$> [1 :: Integer .. 10]

compiledToFromData :: CompiledCode (Either Integer (Maybe (Bool, Integer, Bool)))
compiledToFromData =
  $$( compile
        [||
        let
          v :: Either Integer (Maybe (Bool, Integer, Bool))
          v = Right (Just (True, 1, False))
          d :: PlutusTx.BuiltinData
          d = IsData.toBuiltinData v
         in
          IsData.unsafeFromBuiltinData d
        ||]
    )

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

sumAtIndices :: PlutusTx.BuiltinData -> Integer
sumAtIndices d =
  $( destructList
       "s"
       (Set.fromList [1, 4, 5])
       'list
       [|s1 PlutusTx.+ s4 PlutusTx.+ s5|]
   )
  where
    list :: List Integer
    list = IsData.unsafeFromBuiltinData d

compiledSumAtIndices :: CompiledCode (PlutusTx.BuiltinData -> Integer)
compiledSumAtIndices = $$(compile [||sumAtIndices||])

sumAtIndicesInput :: CompiledCode PlutusTx.BuiltinData
sumAtIndicesInput = liftCodeDef (IsData.toBuiltinData ([0, 10, 20, 30, 40, 50, 60] :: [Integer]))

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
monadicDo =
  $$( compile
        [||
        let x = Just 1
            y = Just 2
         in doExample x y
        ||]
    )

applicative :: CompiledCode (Maybe Integer)
applicative =
  $$( compile
        [||
        let x = Just 1
            y = Just 2
         in applicativeExample x y
        ||]
    )

patternMatch :: CompiledCode (Maybe Integer)
patternMatch =
  $$( compile
        [||
        let x = Just 1
            y = Just 2
         in patternMatchExample x y
        ||]
    )

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
compiledShow =
  $$( compile
        [||
        let x = -1234567890
         in showExample x
        ||]
    )

{-| In this example, the float-in pass cannot reduce the cost unless it allows
unconditionally floating into type abstractions. Both branches are
turned into type abstractions (because the `a + a` branch is not a value). -}
compiledIfThenElse1 :: CompiledCode Integer
compiledIfThenElse1 =
  $$( compile
        [||
        let a = 1 PlutusTx.+ 2
         in if 3 PlutusTx.< (4 :: Integer)
              then 5
              else a PlutusTx.+ a
        ||]
    )

{-| In this example, the float-in pass cannot reduce the cost unless it allows
unconditionally floating into lambda abstractions. Both branches are
lambda abstractions. -}
compiledIfThenElse2 :: CompiledCode Integer
compiledIfThenElse2 =
  $$( compile
        [||
        let a = 1 PlutusTx.+ 2
         in ( if 3 PlutusTx.< (4 :: Integer)
                then \x -> x PlutusTx.+ 5
                else \x -> x PlutusTx.+ a PlutusTx.+ a
            )
              (6 PlutusTx.+ 7)
        ||]
    )

-- TODO: this can be further optimized.
compiledNotNot :: CompiledCode Bool
compiledNotNot =
  $$( compile
        [||
        \x ->
          (\a -> if a then False else True)
            . (\a -> if a then False else True)
            PlutusTx.$ if PlutusTx.lessThanInteger 0 x then True else False
        ||]
    )
    `unsafeApplyCode` liftCodeDef 1

matchAsData :: CompiledCode Integer
matchAsData =
  $$( compile
        [||
        \case
          JustD a -> a
          NothingD -> 1
        ||]
    )
    `unsafeApplyCode` liftCodeDef (JustD 1)

compiledAndWithGHCOpts :: CompiledCode Bool
compiledAndWithGHCOpts =
  let code = $$(compile [||WithGHCOptTest.f||])
   in flip unsafeApplyCode (liftCodeDef (4 :: Integer))
        $ unsafeApplyCode code (liftCodeDef (4 :: Integer))

compiledAndWithoutGHCOpts :: CompiledCode Bool
compiledAndWithoutGHCOpts =
  let code = $$(compile [||WithoutGHCOptTest.f||])
   in flip unsafeApplyCode (liftCodeDef (4 :: Integer))
        $ unsafeApplyCode code (liftCodeDef (4 :: Integer))

compiledAndWithLocal :: CompiledCode Bool
compiledAndWithLocal =
  let f :: Integer -> Integer -> Bool
      f x y = (PlutusTx.&&) (x PlutusTx.< (3 :: Integer)) (y PlutusTx.< (3 :: Integer))
      code = $$(compile [||f||])
   in flip unsafeApplyCode (liftCodeDef (4 :: Integer))
        $ unsafeApplyCode code (liftCodeDef (4 :: Integer))

------------------------------------------------------------------------
-- && vs builtinAnd vs alternatives: boolean AND chaining budget
------------------------------------------------------------------------

-- Pattern 1: Standard && (lazy, delay/force)
andLazyPattern :: Integer -> Integer -> Integer -> Bool
andLazyPattern x y z = (x < 100) && ((y < 100) && (z < 100))
{-# INLINEABLE andLazyPattern #-}

-- Patterns 2 and 4 (builtinAnd, direct BI.ifThenElse) are defined in
-- Budget.BuiltinAndLib with GHC optimisation flags disabled and INLINE pragmas,
-- matching Philip DiSarro's approach in PR #7562.

-- Pattern 3: Multi-way if (negated guards)
andMultiWayIfPattern :: Integer -> Integer -> Integer -> Bool
andMultiWayIfPattern x y z =
  if
    | x >= 100 -> False
    | y >= 100 -> False
    | z >= 100 -> False
    | otherwise -> True
{-# INLINEABLE andMultiWayIfPattern #-}

-- Test scenarios: AllTrue (50,60,70), EarlyFail (150,60,70), LateFail (50,60,150)

-- Pattern 1: Standard &&
andLazy_AllTrue :: CompiledCode Bool
andLazy_AllTrue =
  $$(compile [||andLazyPattern||])
    `unsafeApplyCode` liftCodeDef 50
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 70

andLazy_EarlyFail :: CompiledCode Bool
andLazy_EarlyFail =
  $$(compile [||andLazyPattern||])
    `unsafeApplyCode` liftCodeDef 150
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 70

andLazy_LateFail :: CompiledCode Bool
andLazy_LateFail =
  $$(compile [||andLazyPattern||])
    `unsafeApplyCode` liftCodeDef 50
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 150

-- Pattern 2: builtinAnd (from BuiltinAndLib, with -fno-* flags + INLINE)
andBuiltinAnd_AllTrue :: CompiledCode Bool
andBuiltinAnd_AllTrue =
  $$(compile [||BuiltinAndLib.andBuiltinAndPattern||])
    `unsafeApplyCode` liftCodeDef 50
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 70

andBuiltinAnd_EarlyFail :: CompiledCode Bool
andBuiltinAnd_EarlyFail =
  $$(compile [||BuiltinAndLib.andBuiltinAndPattern||])
    `unsafeApplyCode` liftCodeDef 150
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 70

andBuiltinAnd_LateFail :: CompiledCode Bool
andBuiltinAnd_LateFail =
  $$(compile [||BuiltinAndLib.andBuiltinAndPattern||])
    `unsafeApplyCode` liftCodeDef 50
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 150

-- Pattern 3: Multi-way if
andMultiWayIf_AllTrue :: CompiledCode Bool
andMultiWayIf_AllTrue =
  $$(compile [||andMultiWayIfPattern||])
    `unsafeApplyCode` liftCodeDef 50
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 70

andMultiWayIf_EarlyFail :: CompiledCode Bool
andMultiWayIf_EarlyFail =
  $$(compile [||andMultiWayIfPattern||])
    `unsafeApplyCode` liftCodeDef 150
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 70

andMultiWayIf_LateFail :: CompiledCode Bool
andMultiWayIf_LateFail =
  $$(compile [||andMultiWayIfPattern||])
    `unsafeApplyCode` liftCodeDef 50
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 150

-- Pattern 4: Direct BI.ifThenElse (from BuiltinAndLib, with -fno-* flags + INLINE)
andDirectIfThenElse_AllTrue :: CompiledCode Bool
andDirectIfThenElse_AllTrue =
  $$(compile [||BuiltinAndLib.andDirectIfThenElsePattern||])
    `unsafeApplyCode` liftCodeDef 50
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 70

andDirectIfThenElse_EarlyFail :: CompiledCode Bool
andDirectIfThenElse_EarlyFail =
  $$(compile [||BuiltinAndLib.andDirectIfThenElsePattern||])
    `unsafeApplyCode` liftCodeDef 150
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 70

andDirectIfThenElse_LateFail :: CompiledCode Bool
andDirectIfThenElse_LateFail =
  $$(compile [||BuiltinAndLib.andDirectIfThenElsePattern||])
    `unsafeApplyCode` liftCodeDef 50
    `unsafeApplyCode` liftCodeDef 60
    `unsafeApplyCode` liftCodeDef 150
