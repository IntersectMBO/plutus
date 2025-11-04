{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Redundant if" #-}

module CallTrace.Spec where

import PlutusTx
import PlutusTx.Prelude
import Test.Tasty.Extras (TestNested, testNested, testNestedGhc)
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import CallTrace.Lib
import CallTrace.OtherModule

tests :: TestNested
tests =
  testNested "CallTrace"
    . pure
    $ testNestedGhc
      [ goldenEvalCekTraceWithEmitter
          Cek.logWithCallTraceEmitter
          "nestedLinearFuncions"
          $$(compile [||nestedLinear False||])
      , goldenEvalCekTraceWithEmitter
          Cek.logWithCallTraceEmitter
          "nestedLinearFuncions-error"
          $$(compile [||nestedLinear True||])
      , goldenEvalCekTraceWithEmitter
          Cek.logWithCallTraceEmitter
          "successfullEvaluationYieldsNoTraceLog"
          $$(compile [||functionFromOtherModule False||])
      , goldenEvalCekTraceWithEmitter
          Cek.logWithCallTraceEmitter
          "funcionFromOtherModule-error"
          $$(compile [||functionFromOtherModule True||])
      , goldenEvalCekTraceWithEmitter Cek.logWithCallTraceEmitter "func01" $$(compile [||func 1||])
      , goldenEvalCekTraceWithEmitter Cek.logWithCallTraceEmitter "func02" $$(compile [||func 2||])
      , goldenEvalCekTraceWithEmitter Cek.logWithCallTraceEmitter "func03" $$(compile [||func 3||])
      , goldenEvalCekTraceWithEmitter Cek.logWithCallTraceEmitter "func04" $$(compile [||func 4||])
      , goldenEvalCekTraceWithEmitter Cek.logWithCallTraceEmitter "func05" $$(compile [||func 5||])
      , goldenEvalCekTraceWithEmitter Cek.logWithCallTraceEmitter "func06" $$(compile [||func 6||])
      , goldenEvalCekTraceWithEmitter Cek.logWithCallTraceEmitter "func07" $$(compile [||func 7||])
      , goldenEvalCekTraceWithEmitter Cek.logWithCallTraceEmitter "func08" $$(compile [||func 8||])
      , goldenEvalCekTraceWithEmitter Cek.logWithCallTraceEmitter "func09" $$(compile [||func 9||])
      , goldenEvalCekTraceWithEmitter Cek.logWithCallTraceEmitter "func42" $$(compile [||func 42||])
      ]

bob :: Integer -> Integer -> ()
bob x y =
  if x == y
    then ()
    else error ()

nestedLinear, nestedLinear2, nestedLinear3, nestedLinear4 :: Bool -> BuiltinString
nestedLinear x = nestedLinear2 x
nestedLinear2 x = nestedLinear3 x
nestedLinear3 x = nestedLinear4 x
nestedLinear4 True  = error ()
nestedLinear4 False = error ()

func :: Integer -> BuiltinString
func 1 = trace "func 1" (\_thunk -> nestedLinear True) ()
func 2 = nestedLinear2 True
func 3 = trace "func 3" $ functionFromOtherModule True
func 4 = myClassFunc @Integer 4
func 5 = trace "func 5" $ myClassFunc @Integer 5
func 6 = myClassFunc ()
func 7 = trace "func 7" $ myClassFuncInOtherModule @Integer 7
func 8 = myClassFuncInOtherModule @Integer 8
func 9 = trace "func 9" $ myClassFuncInOtherModule ()
func n =
  if bob 42 n == ()
    then error ()
    else ""

functionFromOtherModule :: Bool -> BuiltinString
functionFromOtherModule x = wraps $ not $ not x

class MyClass a where
  myClassFunc :: a -> BuiltinString

instance MyClass Integer where
  myClassFunc 5 = trace "myClassFunc 5" $ functionFromOtherModule True
  myClassFunc _ = error ()

instance MyClass () where
  myClassFunc () = error ()
