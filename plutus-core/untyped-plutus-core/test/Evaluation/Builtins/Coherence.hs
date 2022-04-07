{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}

-- Turning off all optimization, because otherwise 'toBuiltinMeaning' seems to inline separately for
-- each builtin, causing the simplifier to exhaust all its ticks.
{-# OPTIONS_GHC -O0 #-}

module Evaluation.Builtins.Coherence where

import PlutusPrelude

import PlutusCore
import PlutusCore.Builtin

import Data.Foldable
import Test.Tasty
import Test.Tasty.HUnit

typeSchemeToRuntimeScheme :: TypeScheme val args res -> RuntimeScheme (Length args)
typeSchemeToRuntimeScheme TypeSchemeResult = RuntimeSchemeResult
typeSchemeToRuntimeScheme (TypeSchemeArrow schB) =
    RuntimeSchemeArrow $ typeSchemeToRuntimeScheme schB
typeSchemeToRuntimeScheme (TypeSchemeAll _ schK) =
    RuntimeSchemeAll $ typeSchemeToRuntimeScheme schK

test_TypeSchemesAndRuntimeSchemesAgree :: TestTree
test_TypeSchemesAndRuntimeSchemesAgree =
    testCase "type schemes are coherent with runtime schemes" $
        for_ (enumeration @DefaultFun) $ \fun ->
            case toBuiltinMeaning @_ @_ @(Term TyName Name _ _ ()) fun of
                BuiltinMeaning typeSch _ (BuiltinRuntimeOptions runtimeSch _ _ _) ->
                    typeSchemeToRuntimeScheme typeSch @?= runtimeSch
