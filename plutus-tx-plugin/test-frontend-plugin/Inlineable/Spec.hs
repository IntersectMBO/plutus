{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}

module Inlineable.Spec where

import Inlineable.Lib
import Plinth.Plugin (plinthc)
import PlutusTx.Code
import PlutusTx.Test

import Test.Tasty.Extras

tests :: TestNested
tests =
  testNested ("Inlineable") . pure $
    testNestedGhc
      [ goldenUPlcReadable "triple" tripleCompiled
      ]

tripleCompiled :: CompiledCode (Integer -> (Integer, Integer, Integer))
tripleCompiled = plinthc triple
