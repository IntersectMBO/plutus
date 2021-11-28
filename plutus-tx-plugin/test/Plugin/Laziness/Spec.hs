{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-context #-}

module Plugin.Laziness.Spec where

import Common
import Lib
import PlcTestUtils
import Plugin.Lib

import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Plugin

import Data.Proxy

laziness :: TestNested
laziness = testNested "Laziness" [
    goldenPir "joinError" joinErrorPir
    , goldenUEval "joinErrorEval" [ toUPlc joinErrorPir, toUPlc $ plc (Proxy @"T") True, toUPlc $ plc (Proxy @"F") False]
    , goldenPir "lazyDepUnit" lazyDepUnit
  ]

joinErrorPir :: CompiledCode (Bool -> Bool -> ())
joinErrorPir = plc (Proxy @"joinError") joinError

{-# NOINLINE monoId #-}
monoId :: Builtins.BuiltinByteString -> Builtins.BuiltinByteString
monoId x = x

-- This is a non-value let-binding, so will be delayed, and needs a dependency on Unit
{-# NOINLINE aByteString #-}
aByteString :: Builtins.BuiltinByteString
aByteString = monoId Builtins.emptyByteString

lazyDepUnit :: CompiledCode Builtins.BuiltinByteString
lazyDepUnit = plc (Proxy @"lazyDepUnit") aByteString
