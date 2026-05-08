{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:no-conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:preserve-logging #-}

module Plugin.NoTrace.WithPreservedLogging where

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
