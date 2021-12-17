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

import Budget.Lib (goldenBudget)
import Common
import Lib (goldenPir)

import PlutusTx.Code
import PlutusTx.Prelude qualified as PlutusTx
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

  , goldenBudget "monadicDo" monadicDo
  , goldenPir "monadicDo" monadicDo
  -- These should be a little cheaper than the previous one,
  -- less overhead from going via monadic functions
  , goldenBudget "applicative" applicative
  , goldenPir "applicative" applicative
  , goldenBudget "patternMatch" patternMatch
  , goldenPir "patternMatch" patternMatch
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
