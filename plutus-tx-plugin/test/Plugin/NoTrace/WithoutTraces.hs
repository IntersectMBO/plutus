{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
-- The plugin uses non-conservative optimizations by default and they remove some traces.
-- We disable them to make sure that traces are removed by the 'remove-traces' compiler flag.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:remove-trace #-}

module Plugin.NoTrace.WithoutTraces where

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
