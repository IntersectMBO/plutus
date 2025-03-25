-- editorconfig-checker-disable-file
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
#if !MIN_VERSION_base(4, 15, 0)
{-# OPTIONS_GHC -Wwarn=unrecognised-pragmas #-}
#endif

module Plugin.Laziness.Spec where

import Test.Tasty.Extras

import Plugin.Lib

import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Plugin
import PlutusTx.Test

import Data.Proxy

laziness :: TestNested
laziness = testNested "Laziness" . pure $ testNestedGhc
  [ goldenPirReadable "joinError" joinErrorPir
  , goldenUEval "joinErrorEval" [ toUPlc joinErrorPir, toUPlc $ plc (Proxy @"T") True, toUPlc $ plc (Proxy @"F") False]
  , goldenPirReadable "lazyDepUnit" lazyDepUnit
  ]

joinErrorPir :: CompiledCode (Bool -> Bool -> ())
joinErrorPir = plc (Proxy @"joinError") joinError

monoId :: Builtins.BuiltinByteString -> Builtins.BuiltinByteString
monoId x = x
{-# OPAQUE monoId #-}

-- This is a non-value let-binding, so will be delayed, and needs a dependency on Unit
aByteString :: Builtins.BuiltinByteString
aByteString = monoId Builtins.emptyByteString
{-# OPAQUE aByteString #-}

lazyDepUnit :: CompiledCode Builtins.BuiltinByteString
lazyDepUnit = plc (Proxy @"lazyDepUnit") aByteString
