{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module TH.Unroll.Spec where

import PlutusTx.Code
import Prelude
import Test.Tasty.Extras (TestNested, testNested)

import PlutusTx.Test (goldenBudget, goldenEvalCek, goldenPirReadable, goldenSize,
                      goldenUPlcReadable)
import PlutusTx.TH (compile)
import TH.Unroll.Spec.Lib qualified as Lib

tests :: TestNested
tests =
  testNested
    "TH/Unroll/Golden"
    [ -- Reference fibonacci
      goldenUPlcReadable "fibonacci" fibonacciCode
    , goldenPirReadable "fibonacci" fibonacciCode
    , goldenBudget "fibonacci" fibonacciCode
    , goldenEvalCek "fibonacci" [fibonacciCode]
    , goldenSize "fibonacci" fibonacciCode
    , -- fibonacci with 3 recursion steps inlined manually
      goldenUPlcReadable "fibonacciManuallyUnrolled3" fibonacciManuallyUnrolled3Code
    , goldenPirReadable "fibonacciManuallyUnrolled3" fibonacciManuallyUnrolled3Code
    , goldenBudget "fibonacciManuallyUnrolled3" fibonacciManuallyUnrolled3Code
    , goldenEvalCek "fibonacciManuallyUnrolled3" [fibonacciManuallyUnrolled3Code]
    , goldenSize "fibonacciManuallyUnrolled3" fibonacciManuallyUnrolled3Code
    , -- Fix-based fibonacci
      goldenUPlcReadable "fibonacciFix" fibonacciFixCode
    , goldenPirReadable "fibonacciFix" fibonacciFixCode
    , goldenBudget "fibonacciFix" fibonacciFixCode
    , goldenEvalCek "fibonacciFix" [fibonacciFixCode]
    , goldenSize "fibonacciFix" fibonacciFixCode
    , -- Fix-based fibonaccy with 3 recursion steps inlined manually
      goldenUPlcReadable "fibonacciFixManuallyUnrolled3" fibonacciFixManuallyUnrolled3Code
    , goldenPirReadable "fibonacciFixManuallyUnrolled3" fibonacciFixManuallyUnrolled3Code
    , goldenBudget "fibonacciFixManuallyUnrolled3" fibonacciFixManuallyUnrolled3Code
    , goldenEvalCek "fibonacciFixManuallyUnrolled3" [fibonacciFixManuallyUnrolled3Code]
    , goldenSize "fibonacciFixManuallyUnrolled3" fibonacciFixManuallyUnrolled3Code
    ]

fibonacciCode :: CompiledCode Integer
fibonacciCode = $$(compile [||Lib.fibonacci 15||])

fibonacciManuallyUnrolled3Code :: CompiledCode Integer
fibonacciManuallyUnrolled3Code =
  $$(compile [||Lib.fibonacciManuallyUnrolled3 15||])

fibonacciFixCode :: CompiledCode Integer
fibonacciFixCode = $$(compile [||Lib.fibonacciFix 15||])

fibonacciFixManuallyUnrolled3Code :: CompiledCode Integer
fibonacciFixManuallyUnrolled3Code =
  $$(compile [||Lib.fibonacciFixManuallyUnrolled3 15||])
