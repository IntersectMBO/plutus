{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:generate-callstack #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Redundant if" #-}

module Plugin.CallStack.Spec where

import PlutusTx
import PlutusTx.Prelude
import Prelude ()

import PlutusTx.Test (goldenEvalCekTraceCatchBudget)

import Test.Tasty.Extras (TestNested, testNested, testNestedGhc)

import Plugin.CallStack.OtherModule

callstack :: TestNested
callstack =
  testNested "CallStack" . pure $
    testNestedGhc
      [ goldenEvalCekTraceCatchBudget "nestedLinearFuncions" $$(compile [||nestedLinear False||])
      , goldenEvalCekTraceCatchBudget "nestedLinearFuncions-error" $$(compile [||nestedLinear True||])
      , goldenEvalCekTraceCatchBudget
          "funcionFromOtherModule"
          $$(compile [||functionFromOtherModule False||])
      , goldenEvalCekTraceCatchBudget
          "funcionFromOtherModule-error"
          $$(compile [||functionFromOtherModule True||])
      , goldenEvalCekTraceCatchBudget "func01" $$(compile [||func 1||])
      , goldenEvalCekTraceCatchBudget "func02" $$(compile [||func 2||])
      , goldenEvalCekTraceCatchBudget "func03" $$(compile [||func 3||])
      , goldenEvalCekTraceCatchBudget "func04" $$(compile [||func 4||])
      , goldenEvalCekTraceCatchBudget "func05" $$(compile [||func 5||])
      , goldenEvalCekTraceCatchBudget "func06" $$(compile [||func 6||])
      , goldenEvalCekTraceCatchBudget "func07" $$(compile [||func 7||])
      , goldenEvalCekTraceCatchBudget "func08" $$(compile [||func 8||])
      , goldenEvalCekTraceCatchBudget "func09" $$(compile [||func 9||])
      , goldenEvalCekTraceCatchBudget "func42" $$(compile [||func 42||])
      ]

bob :: Integer -> Integer -> ()
bob x y =
  if x == y
  then ()
  else traceError callStack

nestedLinear, nestedLinear2, nestedLinear3, nestedLinear4 :: Bool -> BuiltinString
nestedLinear x = nestedLinear2 x
nestedLinear2 x = nestedLinear3 x
nestedLinear3 x = nestedLinear4 x
nestedLinear4 True  = traceError callStack
nestedLinear4 False = callStack

func :: Integer -> BuiltinString
func 1 = nestedLinear True
func 2 = nestedLinear2 True
func 3 = functionFromOtherModule True
func 4 = myClassFunc @Integer 4
func 5 = myClassFunc @Integer 5
func 6 = myClassFunc ()
func 7 = myClassFuncInOtherModule @Integer 7
func 8 = myClassFuncInOtherModule @Integer 8
func 9 = myClassFuncInOtherModule ()
func n =
  if bob 42 n == ()
  then traceError callStack
  else ""

functionFromOtherModule :: Bool -> BuiltinString
functionFromOtherModule x = wraps (not $ not x)

class MyClass a where
  myClassFunc :: a -> BuiltinString

instance MyClass Integer where
  myClassFunc 5 = functionFromOtherModule True
  myClassFunc _ = traceError callStack

instance MyClass () where
  myClassFunc () = traceError callStack
