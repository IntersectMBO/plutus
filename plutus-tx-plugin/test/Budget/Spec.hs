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
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-context #-}


module Budget.Spec where

import Test.Tasty.Extras

import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import PlutusTx.Test (goldenBudget, goldenPir)
import PlutusTx.TH (compile)

tests :: TestNested
tests = testNested "Budget" [
    goldenBudget "sum" compiledSum
  , goldenPir "sum" compiledSum

  , goldenBudget "any" compiledAny
  , goldenPir "any" compiledAny

  , goldenBudget "find" compiledFind
  , goldenPir "find" compiledFind

  , goldenBudget "filter" compiledFilter
  , goldenPir "filter" compiledFilter

  , goldenBudget "elem" compiledElem
  , goldenPir "elem" compiledElem

  , goldenBudget "toFromData" compiledToFromData
  , goldenPir "toFromData" compiledToFromData

  , goldenBudget "monadicDo" monadicDo
  , goldenPir "monadicDo" monadicDo
  -- These should be a little cheaper than the previous one,
  -- less overhead from going via monadic functions
  , goldenBudget "applicative" applicative
  , goldenPir "applicative" applicative
  , goldenBudget "patternMatch" patternMatch
  , goldenPir "patternMatch" patternMatch
  , goldenBudget "show" compiledShow
  , goldenPir "show" compiledShow
  ]

compiledSum :: CompiledCode Integer
compiledSum = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.sum ls ||])

compiledAny :: CompiledCode Bool
compiledAny = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.any ((PlutusTx.>) 10) ls ||])

compiledFind :: CompiledCode (Maybe Integer)
compiledFind = $$(compile [||
      let ls = [1,2,3,4,5,6,7,8,9,10] :: [Integer]
       in PlutusTx.find ((PlutusTx.>) 10) ls ||])

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
