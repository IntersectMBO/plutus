-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import PlutusPrelude

import AnalysisSpec
import Check.Spec
import GeneratorSpec
import NamesSpec
import ParserSpec
import TransformSpec
import TypeSpec

import PlutusCore qualified as PLC
import PlutusIR
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Parser (Parser, pTerm)
import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

import Flat (flat, unflat)

main :: IO ()
main = defaultMain $ runTestNestedIn ["plutus-ir/test"] tests

pTermAsProg :: Parser (Program TyName Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan)
pTermAsProg = fmap (Program mempty PLC.latestVersion) pTerm

tests :: TestNested
tests = testGroup "plutus-ir" <$> sequence
    [ prettyprinting
    , prettyprintingReadable
    , parsing
    , lets
    , datatypes
    , recursion
    , serialization
    , errors
    , pure names
    , transform
    , types
    , typeErrors
    , generators 1
    , pure uniqueness
    , evalOrder
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
    , goldenPlcFromPirCatch pTermAsProg "idleAll"
    , goldenPlcFromPirCatch pTermAsProg "some"
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
    [ goldenPlcFromPirCatch pTermAsProg "mutuallyRecursiveTypes"
    , goldenPlcFromPirCatch pTermAsProg "recursiveTypeBind"
    ]
