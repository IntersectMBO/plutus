{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}

-- | Verifies that the Strict extension is automatically set by the driver plugin.
module Strict.Spec where

import Plinth.Plugin (plinthc)
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.Test

import Test.Tasty.Extras

tests :: TestNested
tests =
  testNested ("Strict") . pure $
    testNestedGhc
      [ goldenPirReadable "strict" strict
      ]

strict :: CompiledCode (Integer -> Integer -> Integer)
strict =
  plinthc
    ( \x ->
        let y = PlutusTx.divideInteger 42 x
         in \z -> PlutusTx.addInteger y z
    )
