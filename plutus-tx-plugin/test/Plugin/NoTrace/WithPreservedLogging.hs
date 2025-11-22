{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:preserve-logging #-}

module Plugin.NoTrace.WithPreservedLogging where

import Data.Proxy (Proxy (..))
import Plugin.NoTrace.Lib qualified as Lib
import PlutusTx.Bool (Bool)
import PlutusTx.Builtins (BuiltinString, Integer)
import PlutusTx.Code (CompiledCode)
import PlutusTx.Plugin (plc)

traceArgument :: CompiledCode (BuiltinString -> ())
traceArgument = plc (Proxy @"traceArgument") Lib.traceArgument

traceShow :: CompiledCode ()
traceShow = plc (Proxy @"traceShow") Lib.traceShow

traceDirect :: CompiledCode ()
traceDirect = plc (Proxy @"traceDirect") Lib.traceDirect

traceNonConstant :: CompiledCode (BuiltinString -> BuiltinString)
traceNonConstant = plc (Proxy @"traceNonConstant") Lib.traceNonConstant

traceComplex :: CompiledCode (Bool -> ())
traceComplex = plc (Proxy @"traceComplex") Lib.traceComplex

traceRepeatedly :: CompiledCode Integer
traceRepeatedly = plc (Proxy @"traceRepeatedly") Lib.traceRepeatedly

traceImpure :: CompiledCode ()
traceImpure = plc (Proxy @"traceImpure") Lib.traceImpure
