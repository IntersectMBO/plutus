{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}

module Plugin.Laziness.Spec where

import           Common
import           PlcTestUtils
import           Plugin.Lib

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Plugin

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

laziness :: TestNested
laziness = testNested "Laziness" [
    goldenPir "joinError" joinErrorPir
    , goldenEval "joinErrorEval" [ getProgram joinErrorPir, getProgram $ plc @"T" True, getProgram $ plc @"F" False]
    , goldenPir "lazyDepUnit" lazyDepUnit
  ]

joinErrorPir :: CompiledCode (Bool -> Bool -> ())
joinErrorPir = plc @"joinError" joinError

{-# NOINLINE monoId #-}
monoId :: Builtins.ByteString -> Builtins.ByteString
monoId x = x

-- This is a non-value let-binding, so will be delayed, and needs a dependency on Unit
{-# NOINLINE aByteString #-}
aByteString :: Builtins.ByteString
aByteString = monoId Builtins.emptyByteString

lazyDepUnit :: CompiledCode (Builtins.ByteString)
lazyDepUnit = plc @"lazyDepUnit" aByteString
