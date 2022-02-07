{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-all #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}

module Plugin.Strict.Spec (strict, strictAddExample, strictAppendExample) where

import Test.Tasty.Extras

import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Plugin
import PlutusTx.Prelude qualified as P

import Data.Proxy

strict :: TestNested
strict = testNested "Strict" [
    goldenPir "strictAdd" strictAdd
  , goldenPir "strictAppend" strictAppend
  , goldenPir "strictAppend2" strictAppend2
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
