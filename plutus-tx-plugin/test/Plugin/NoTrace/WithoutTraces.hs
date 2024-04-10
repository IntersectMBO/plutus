{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
-- The plugin uses non-conservative optimizations by default and they remove some traces.
-- We disable them to make sure that traces are removed by the 'remove-traces' compiler flag.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:remove-trace #-}

module Plugin.NoTrace.WithoutTraces where

import PlutusTx (CompiledCode, compile)
import PlutusTx.Builtins qualified as B
import PlutusTx.Prelude qualified as P

trace :: CompiledCode (B.BuiltinString -> ())
trace = $$(compile [||\(x :: B.BuiltinString) -> B.trace x ()||])

traceDirect :: CompiledCode ()
traceDirect = $$(compile [||B.trace "test" ()||])

tracePrelude :: CompiledCode Integer
tracePrelude = $$(compile [||P.trace "test" (1 :: Integer)||])

traceComplex :: CompiledCode (Bool -> ())
traceComplex =
  $$(compile [||\(b :: Bool) -> if b then P.trace "yes" () else P.traceError "no" ()||])

traceRepeatedly :: CompiledCode P.Integer
traceRepeatedly =
  $$( compile
        [||
        let i1 = P.trace "Making my first int" (1 :: P.Integer)
            i2 = P.trace "Making my second int" (2 :: P.Integer)
            i3 = P.trace "Adding them up" (i1 P.+ i2)
         in i3
        ||]
    )
