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

import           Budget.Lib       (goldenBudget)
import           Common
import           Lib              (goldenPir)

import           PlutusTx.Code
import qualified PlutusTx.Prelude as PlutusTx
import           PlutusTx.TH      (compile)

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

