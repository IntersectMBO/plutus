{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:no-strict #-}

{-| Verifies that the Strict extension, which the driver plugin sets by default,
can be unset via `no-strict`. -}
module NoStrict.Spec where

import Plinth.Plugin (plinthc)
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.Test

import Test.Tasty.Extras

tests :: TestNested
tests =
  testNested ("NoStrict") . pure $
    testNestedGhc
      [ goldenPirReadable "nostrict" nostrict
      ]

nostrict :: CompiledCode (Integer -> Integer -> Integer)
nostrict =
  plinthc
    ( \x ->
        let y = PlutusTx.divideInteger 42 x
         in \z -> PlutusTx.addInteger y z
    )
