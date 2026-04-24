-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-uplc=0 #-}

module Plugin.Laziness.Spec where

import Test.Tasty.Extras

import Plugin.Lib

import Plinth.Plugin
import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Test

laziness :: TestNested
laziness =
  testNested "Laziness" . pure $
    testNestedGhc
      [ goldenPirReadable "joinError" joinErrorPir
      , goldenUEval
          "joinErrorEval"
          [toUPlc joinErrorPir, toUPlc $ plinthc True, toUPlc $ plinthc False]
      , goldenPirReadable "lazyDepUnit" lazyDepUnit
      ]

joinErrorPir :: CompiledCode (Bool -> Bool -> ())
joinErrorPir = plinthc joinError

monoId :: Builtins.BuiltinByteString -> Builtins.BuiltinByteString
monoId x = x
{-# OPAQUE monoId #-}

-- This is a non-value let-binding, so will be delayed, and needs a dependency on Unit
aByteString :: Builtins.BuiltinByteString
aByteString = monoId Builtins.emptyByteString
{-# OPAQUE aByteString #-}

lazyDepUnit :: CompiledCode Builtins.BuiltinByteString
lazyDepUnit = plinthc aByteString
