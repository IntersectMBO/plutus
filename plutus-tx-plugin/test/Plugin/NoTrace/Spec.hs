-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:remove-trace #-}

module Plugin.NoTrace.Spec where

import Test.Tasty.Extras

import Data.Proxy
import Prelude qualified as H

import PlutusTx
import PlutusTx.Builtins qualified as B
import PlutusTx.Plugin
import PlutusTx.Prelude qualified as P
import PlutusTx.Test

noTrace :: TestNested
noTrace = testNestedGhc "NoTrace"
  [ goldenPir "trace" trace
  , goldenPir "traceComplex" traceComplex
  , goldenEvalCekLog "traceDirect" [traceDirect]
  , goldenEvalCekLog "tracePrelude" [tracePrelude]
  , goldenEvalCekLog "traceRepeatedly" [traceRepeatedly]
  ]

-- Half-stolen from Plugin.Primitives.Spec
trace :: CompiledCode (B.BuiltinString -> ())
trace = plc (Proxy @"trace") (\(x :: B.BuiltinString) -> B.trace x ())

traceComplex :: CompiledCode (H.Bool -> ())
traceComplex = plc (Proxy @"traceComplex") (\(b :: H.Bool) -> if b then P.trace "yes" () else P.traceError "no")

-- Half-stolen from TH.Spec
traceDirect :: CompiledCode ()
traceDirect = $$(compile [|| B.trace "test" () ||])

tracePrelude :: CompiledCode H.Integer
tracePrelude = $$(compile [|| P.trace "test" (1::H.Integer) ||])

traceRepeatedly :: CompiledCode P.Integer
traceRepeatedly = $$(compile
  [||
    let i1 = P.trace "Making my first int" (1::P.Integer)
        i2 = P.trace "Making my second int" (2::P.Integer)
        i3 = P.trace "Adding them up" (i1 P.+ i2)
    in i3
  ||])
