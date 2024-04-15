{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module Plugin.NoTrace.Spec where

import Prelude

import Plugin.NoTrace.Lib (countTraces)
import Plugin.NoTrace.WithoutTraces qualified as WithoutTraces
import Plugin.NoTrace.WithTraces qualified as WithTraces
import Test.Tasty (testGroup)
import Test.Tasty.Extras (TestNested)
import Test.Tasty.HUnit (testCase, (@=?))

noTrace :: TestNested
noTrace = pure do
  testGroup
    "remove-trace"
    [ testGroup
        "Trace calls are present"
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
        ]
    , testGroup
        "Trace calls are absent"
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
        ]
    ]
