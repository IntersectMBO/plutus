{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-context #-}

module Plugin.Strict.Spec (strict) where

import Test.Tasty.Extras

import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Code
import PlutusTx.Plugin
import PlutusTx.Prelude qualified as P
import PlutusTx.Test

import Data.Proxy

strict :: TestNested
strict = testNested "Strict" [
    goldenPir "strictAdd" strictAdd
  , goldenPir "strictAppend" strictAppend
  , goldenPir "strictAppend2" strictAppend2
  , goldenPir "strictAppendString" strictAppendString
  , goldenPir "strictITE" strictITE
  , goldenPir "strictPair" strictPair
  , goldenPir "strictList" strictList
  , goldenPir "strictData" strictData
  ]

strictAdd :: CompiledCode (Integer -> Integer -> Integer)
strictAdd = plc (Proxy @"strictLet") strictAddExample

strictAddExample :: Integer -> Integer -> Integer
strictAddExample !x !y = Builtins.addInteger x y

strictAppend :: CompiledCode (P.BuiltinByteString -> P.BuiltinByteString -> P.BuiltinByteString)
strictAppend = plc (Proxy @"strictLet") strictAppendExample

strictAppendExample :: P.BuiltinByteString -> P.BuiltinByteString -> P.BuiltinByteString
strictAppendExample !x !y = Builtins.appendByteString x y

strictAppend2 :: CompiledCode (Wrapper -> Wrapper -> Wrapper)
strictAppend2 = plc (Proxy @"strictLet") strictAppend2Example

strictAppend2Example :: Wrapper -> Wrapper -> Wrapper
strictAppend2Example !(Wrapper x) !(Wrapper y) = Wrapper (Builtins.appendByteString x y)

-- Wrapper, like PubKeyHash etc.
newtype Wrapper = Wrapper P.BuiltinByteString

strictAppendString :: CompiledCode (P.BuiltinString -> P.BuiltinString -> P.BuiltinString)
strictAppendString = plc (Proxy @"strictAppendString") strictAppendStringExample

strictAppendStringExample :: P.BuiltinString -> P.BuiltinString -> P.BuiltinString
strictAppendStringExample !x !y = Builtins.appendString x y

strictITE :: CompiledCode (BI.BuiltinBool -> Integer -> Integer -> Integer)
strictITE = plc (Proxy @"strictITE") strictITEExample

strictITEExample :: BI.BuiltinBool -> Integer -> Integer -> Integer
strictITEExample !x !y !z = BI.ifThenElse x y z

strictPair :: CompiledCode (BI.BuiltinPair Integer Integer -> Integer)
strictPair = plc (Proxy @"strictPair") strictPairExample

strictPairExample :: BI.BuiltinPair Integer Integer -> Integer
strictPairExample !p = BI.fst p

strictList :: CompiledCode (BI.BuiltinList Integer -> Integer)
strictList = plc (Proxy @"strictList") strictListExample

strictListExample :: BI.BuiltinList Integer -> Integer
strictListExample !p = BI.head p

strictData :: CompiledCode (BI.BuiltinData -> Integer)
strictData = plc (Proxy @"strictData") strictDataExample

strictDataExample :: BI.BuiltinData -> Integer
strictDataExample !d = BI.unsafeDataAsI d
