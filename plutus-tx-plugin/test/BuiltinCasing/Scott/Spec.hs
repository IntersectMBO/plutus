{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:target-version=1.0.0 #-}

module BuiltinCasing.Scott.Spec (tests) where

import Test.Tasty.Extras

import PlutusTx (CompiledCode, compile, unsafeApplyCode)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Prelude
import PlutusTx.Test

integerCase :: CompiledCode (Integer -> BuiltinString)
integerCase = $$(compile [||integerCaseWithTrace||])

integerZero :: CompiledCode Integer
integerZero = $$(compile [||0||])

integerTwo :: CompiledCode Integer
integerTwo = $$(compile [||2||])

integerCaseWithTrace :: Integer -> BuiltinString
integerCaseWithTrace i =
  Builtins.caseInteger
    ( Builtins.trace
        "scrutinee"
        ( Builtins.divideInteger
            (Builtins.addInteger (Builtins.multiplyInteger i i) i)
            3
        )
    )
    [ Builtins.trace "branch 0" "a"
    , Builtins.trace "branch 1" "b"
    , Builtins.trace "branch 2" "c"
    ]

tests :: TestNested
tests =
  testNested "BuiltinCasing/Scott"
    . pure
    $ testNestedGhc
      [ goldenPirReadable "integerCase" integerCase
      , goldenEvalCekLog
          "integerCaseFirst"
          (integerCase `unsafeApplyCode` integerZero)
      , goldenEvalCekLog
          "integerCaseThird"
          (integerCase `unsafeApplyCode` integerTwo)
      , goldenEvalCekCatchBudget
          "integerCaseThirdBudget"
          (integerCase `unsafeApplyCode` integerTwo)
      ]
