{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}

module Plugin.Laziness.Spec where

import           Common
import           Lib
import           PlcTestUtils
import           Plugin.Lib

import qualified Language.PlutusTx.Builtins   as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Plugin

import qualified Language.PlutusCore.Universe as PLC

import           Data.Proxy

laziness :: TestNested
laziness = testNested "Laziness" [
    goldenPir "joinError" joinErrorPir
    , goldenUEval "joinErrorEval" [ toUPlc joinErrorPir, toUPlc $ plc (Proxy @"T") True, toUPlc $ plc (Proxy @"F") False]
    , goldenPir "lazyDepUnit" lazyDepUnit
  ]

joinErrorPir :: CompiledCode PLC.DefaultUni (Bool -> Bool -> ())
joinErrorPir = plc (Proxy @"joinError") joinError

{-# NOINLINE monoId #-}
monoId :: Builtins.ByteString -> Builtins.ByteString
monoId x = x

-- This is a non-value let-binding, so will be delayed, and needs a dependency on Unit
{-# NOINLINE aByteString #-}
aByteString :: Builtins.ByteString
aByteString = monoId Builtins.emptyByteString

lazyDepUnit :: CompiledCode PLC.DefaultUni Builtins.ByteString
lazyDepUnit = plc (Proxy @"lazyDepUnit") aByteString
