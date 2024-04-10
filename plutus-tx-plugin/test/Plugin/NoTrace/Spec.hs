{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module Plugin.NoTrace.Spec where

import Prelude

import Control.Lens (universeOf, (^.))
import Plugin.NoTrace.WithoutTraces qualified as WithoutTraces
import Plugin.NoTrace.WithTraces qualified as WithTraces
import PlutusCore.Default.Builtins qualified as Builtin
import PlutusTx.Code (CompiledCode, getPlcNoAnn)
import Test.Tasty (testGroup)
import Test.Tasty.Extras (TestNested)
import Test.Tasty.HUnit (testCase, (@=?))
import UntypedPlutusCore.Core qualified as UPLC

noTrace :: TestNested
noTrace = pure do
  testGroup
    "remove-trace"
    [ testGroup
        "Trace calls are present"
        [ testCase "trace" $
            1 @=? countTraces WithTraces.trace
        , testCase "trace-complex" $
            2 @=? countTraces WithTraces.traceComplex
        , testCase "trace-direct" $
            1 @=? countTraces WithTraces.traceDirect
        , testCase "trace-prelude" $
            1 @=? countTraces WithTraces.tracePrelude
        , testCase "trace-repeatedly" $
            3 @=? countTraces WithTraces.traceRepeatedly
        ]
    , testGroup
        "Trace calls are absent"
        [ testCase "trace" $
            0 @=? countTraces WithoutTraces.trace
        , testCase "trace-complex" $
            0 @=? countTraces WithoutTraces.traceComplex
        , testCase "trace-direct" $
            0 @=? countTraces WithoutTraces.traceDirect
        , testCase "trace-prelude" $
            0 @=? countTraces WithoutTraces.tracePrelude
        , testCase "trace-repeatedly" $
            0 @=? countTraces WithoutTraces.traceRepeatedly
        ]
    ]

countTraces :: CompiledCode a -> Int
countTraces code =
  length
    [ subterm
    | subterm@(UPLC.Builtin _ Builtin.Trace) <-
        universeOf UPLC.termSubterms (getPlcNoAnn code ^. UPLC.progTerm)
    ]
