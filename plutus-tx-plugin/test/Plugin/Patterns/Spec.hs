{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-uplc=0 #-}

module Plugin.Patterns.Spec where

import Test.Tasty.Extras

import Plinth.Plugin
import PlutusCore.Test ()
import PlutusTx.Code
import PlutusTx.Prelude as P
import PlutusTx.Test

data Example a = EInt Integer | ETwo a a

pattern EInt' i = EInt i

pattern ETwoBoth a b = ETwo a b
pattern ETwo2 b <- ETwo _ b

pattern ERec {hello, world} <- ETwo hello world
  where
    ERec hello world = ETwo hello world

psym1 :: CompiledCode (Example BuiltinString -> Integer)
psym1 =
  plinthc
    ( \(e :: Example BuiltinString) ->
        case e of
          EInt' i -> i
          ETwo2 _ -> 1
          _ -> 0
    )

psymRec :: CompiledCode BuiltinString
psymRec =
  plinthc
    ( let r = ERec {hello = "wot", world = "yo"}
       in case r of
            ERec {world} -> world
            _ -> "no"
    )

patterns :: TestNested
patterns =
  testNested "Patterns" Prelude.. Prelude.pure Prelude.$
    testNestedGhc
      [ goldenPirReadable "psym1" psym1
      , goldenPirReadable "psymRec" psymRec
      ]
