-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Spec where

import PlutusPrelude

import TransformSpec ()

import PlutusCore qualified as PLC
import PlutusIR
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Parser (Parser, pTerm)
import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

import Flat (flat, unflat)

pTermAsProg :: Parser (Program TyName Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan)
pTermAsProg = fmap (Program mempty PLC.latestVersion) pTerm

test_misc :: TestTree
test_misc = runTestNestedIn ["plutus-ir/test"] $ testGroup "plutus-ir" <$> sequence
    [ prettyprinting
    , prettyprintingReadable
    , lets
    , datatypes
    , recursion
    , serialization
    , errors
    ]

prettyprinting :: TestNested
prettyprinting = testNested "prettyprinting"
    $ map (goldenPir id pTerm)
    [ "basic"
    , "maybe"
    ]

prettyprintingReadable :: TestNested
prettyprintingReadable = testNested "prettyprintingReadable"
    $ map (goldenPirDoc prettyPirReadable pTerm)
    [ "basic"
    , "maybe"
    , "letInLet"
    , "letDep"
    , "listMatch"
    , "idleAll"
    , "some"
    , "even3"
    , "stupidZero"
    , "mutuallyRecursiveValues"
    , "errorBinding"
    , "some"
    , "stupidZero"
    , "recursiveTypeBind"
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

serialization :: TestNested
serialization = testNested "serialization"
    $ map (goldenPir roundTripPirTerm pTerm)
    [ "serializeBasic"
    , "serializeMaybePirTerm"
    , "serializeEvenOdd"
    , "serializeListMatch"
    ]

roundTripPirTerm :: Term TyName Name PLC.DefaultUni PLC.DefaultFun a -> Term TyName Name PLC.DefaultUni PLC.DefaultFun ()
roundTripPirTerm = decodeOrError . unflat . flat . void
  where
    decodeOrError (Right tm) = tm
    decodeOrError (Left err) = error (show err)

errors :: TestNested
errors = testNested "errors"
    [ goldenPlcFromPir pTermAsProg "mutuallyRecursiveTypes"
    , goldenPlcFromPir pTermAsProg "recursiveTypeBind"
    ]
