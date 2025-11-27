{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module Plugin.NoTrace.Spec where

import Prelude

import Plugin.NoTrace.Lib (countTraces)
import Plugin.NoTrace.WithPreservedLogging qualified as WithPreservedLogging
import Plugin.NoTrace.WithTraces qualified as WithTraces
import Plugin.NoTrace.WithoutTraces qualified as WithoutTraces
import PlutusTx.Test.Run.Code (evaluatesToError, evaluatesWithoutError)
import Test.Tasty (testGroup)
import Test.Tasty.Extras (TestNested, embed)
import Test.Tasty.HUnit (assertBool, testCase, (@=?))

noTrace :: TestNested
noTrace = embed do
  testGroup
    "remove-trace"
    [ testGroup
        "Trace calls are preserved (no-remove-trace)"
        [ testCase "trace-argument" $
            1 @=? countTraces WithTraces.traceArgument
        , testCase "trace-show" $
            1 @=? countTraces WithTraces.traceShow
        , testCase "trace-complex" $
            2 @=? countTraces WithTraces.traceComplex
        , testCase "trace-direct" $
            1 @=? countTraces WithTraces.traceDirect
        , testCase "trace-non-constant" $
            1 @=? countTraces WithTraces.traceNonConstant
        , testCase "trace-repeatedly" $
            3 @=? countTraces WithTraces.traceRepeatedly
        , testCase "trace-impure" $
            1 @=? countTraces WithTraces.traceImpure
        , testCase "trace-impure with effect" $ -- See Note [Impure trace messages]
            assertBool "Effect is missing" (evaluatesToError WithTraces.traceImpure)
        ]
    , testGroup
        "Trace calls are preserved (preserve-logging)"
        [ testCase "trace-argument" $
            1 @=? countTraces WithPreservedLogging.traceArgument
        , testCase "trace-show" $
            1 @=? countTraces WithPreservedLogging.traceShow
        , testCase "trace-complex" $
            2 @=? countTraces WithPreservedLogging.traceComplex
        , testCase "trace-direct" $
            1 @=? countTraces WithPreservedLogging.traceDirect
        , testCase "trace-non-constant" $
            1 @=? countTraces WithPreservedLogging.traceNonConstant
        , testCase "trace-repeatedly" $
            3 @=? countTraces WithPreservedLogging.traceRepeatedly
        , testCase "trace-impure" $
            1 @=? countTraces WithPreservedLogging.traceImpure
        , testCase "trace-impure with effect" $ -- See Note [Impure trace messages]
            assertBool "Effect is missing" (evaluatesToError WithPreservedLogging.traceImpure)
        ]
    , testGroup
        "Trace calls are removed (remove-trace)"
        [ testCase "trace-argument" $
            0 @=? countTraces WithoutTraces.traceArgument
        , testCase "trace-show" $
            0 @=? countTraces WithoutTraces.traceShow
        , testCase "trace-complex" $
            0 @=? countTraces WithoutTraces.traceComplex
        , testCase "trace-direct" $
            0 @=? countTraces WithoutTraces.traceDirect
        , testCase "trace-non-constant" $
            0 @=? countTraces WithoutTraces.traceNonConstant
        , testCase "trace-repeatedly" $
            0 @=? countTraces WithoutTraces.traceRepeatedly
        , testCase "trace-impure" $
            0 @=? countTraces WithoutTraces.traceImpure
        , testCase "trace-impure without effect" $ -- See Note [Impure trace messages]
            assertBool "Effect wasn't erased" (evaluatesWithoutError WithoutTraces.traceImpure)
        ]
    ]
