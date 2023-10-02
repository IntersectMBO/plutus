-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module PlutusIR.Compiler.Tests where

import PlutusCore qualified as PLC
import PlutusIR
import PlutusIR.Parser (Parser, pTerm)
import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

instance Semigroup PLC.SrcSpan where
    sp1 <> _ = sp1

instance Monoid PLC.SrcSpan where
    mempty = initialSrcSpan ""

pTermAsProg :: Parser (Program TyName Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan)
pTermAsProg = fmap (Program mempty PLC.latestVersion) pTerm

test_compiler :: TestTree
test_compiler = runTestNestedIn ["plutus-ir/test/PlutusIR"] $ testNested "Compiler"
    [ lets
    , datatypes
    , recursion
    , errors
    ]

lets :: TestNested
lets = testNested "lets"
    [ goldenPlcFromPir pTermAsProg "letInLet"
    , goldenPlcFromPir pTermAsProg "letDep"
    ]

datatypes :: TestNested
datatypes = testNested "datatypes"
    [ goldenPlcFromPir pTermAsProg "maybe"
    , goldenPlcFromPir pTermAsProg "listMatch"
    , goldenPlcFromPir pTermAsProg "idleAll"
    , goldenPlcFromPir pTermAsProg "some"
    , goldenEvalPir pTermAsProg "listMatchEval"
    , goldenTypeFromPir topSrcSpan pTerm "dataEscape"
    , testNested "scott"
        [ goldenPlcFromPirScott pTermAsProg "maybe"
        , goldenPlcFromPirScott pTermAsProg "listMatch"
        ]
    ]

recursion :: TestNested
recursion = testNested "recursion"
    [ goldenNamedUPlcFromPir pTermAsProg "factorial"
    , goldenPlcFromPir pTermAsProg "even3"
    , goldenEvalPir pTermAsProg "even3Eval"
    , goldenPlcFromPir pTermAsProg "stupidZero"
    , goldenPlcFromPir pTermAsProg "mutuallyRecursiveValues"
    , goldenEvalPir pTermAsProg "errorBinding"
    ]

errors :: TestNested
errors = testNested "errors"
    [ goldenPlcFromPir pTermAsProg "mutuallyRecursiveTypes"
    , goldenPlcFromPir pTermAsProg "recursiveTypeBind"
    ]
