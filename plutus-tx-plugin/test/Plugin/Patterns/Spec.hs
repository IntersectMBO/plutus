{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Plugin.Patterns.Spec where

import Test.Tasty.Extras

import PlutusCore.Test ()
import PlutusTx.Code
import PlutusTx.Plugin
import PlutusTx.Prelude as P
import PlutusTx.Test

import Data.Proxy

data Example a = EInt Integer | ETwo a a

pattern EInt' i = EInt i

pattern ETwoBoth a b = ETwo a b
pattern ETwo2 b <- ETwo a b

pattern ERec {hello, world} <- ETwo hello world
  where ERec hello world = ETwo hello world

psym1 :: CompiledCode (Example BuiltinString -> Integer)
psym1 = plc (Proxy @"psym1") (
  \(e :: Example BuiltinString) ->
    case e of
      EInt' i -> i
      ETwo2 s -> 1
      _       -> 0
  )

psymRec :: CompiledCode BuiltinString
psymRec = plc (Proxy @"psymRec") (
  let r = ERec { hello = "wot", world = "yo" }
  in case r of
      ERec{world} -> world
      _           -> "no"
  )

patterns :: TestNested
patterns = testNestedGhc "Patterns" [
    goldenPirReadable "psym1" psym1
    , goldenPirReadable "psymRec" psymRec
  ]
