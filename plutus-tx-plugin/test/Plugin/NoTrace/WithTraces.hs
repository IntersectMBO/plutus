{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
-- The plugin uses non-conservative optimizations by default and they remove some traces.
-- We disable them to make sure that no traces are removed.
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:no-remove-trace #-}

module Plugin.NoTrace.WithTraces where

import Plinth.Plugin (plinthc)
import Plugin.NoTrace.Lib qualified as Lib
import PlutusTx.Bool (Bool)
import PlutusTx.Builtins (BuiltinString, Integer)
import PlutusTx.Code (CompiledCode)

traceArgument :: CompiledCode (BuiltinString -> ())
traceArgument = plinthc Lib.traceArgument

traceShow :: CompiledCode ()
traceShow = plinthc Lib.traceShow

traceDirect :: CompiledCode ()
traceDirect = plinthc Lib.traceDirect

traceNonConstant :: CompiledCode (BuiltinString -> BuiltinString)
traceNonConstant = plinthc Lib.traceNonConstant

traceComplex :: CompiledCode (Bool -> ())
traceComplex = plinthc Lib.traceComplex

traceRepeatedly :: CompiledCode Integer
traceRepeatedly = plinthc Lib.traceRepeatedly

traceImpure :: CompiledCode ()
traceImpure = plinthc Lib.traceImpure
