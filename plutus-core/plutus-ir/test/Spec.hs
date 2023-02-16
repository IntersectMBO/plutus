-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import PlutusPrelude

import GeneratorSpec
import NamesSpec
import ParserSpec
import TransformSpec
import TypeSpec

import PlutusCore qualified as PLC
import PlutusIR
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Parser (pTerm)
import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

import Flat (flat, unflat)

main :: IO ()
main = defaultMain $ runTestNestedIn ["plutus-ir/test"] tests

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
    [ goldenPlcFromPir pTerm "letInLet"
    , goldenPlcFromPir pTerm "letDep"
    ]

datatypes :: TestNested
datatypes = testNested "datatypes"
    [ goldenPlcFromPir pTerm "maybe"
    , goldenPlcFromPir pTerm "listMatch"
    , goldenPlcFromPirCatch pTerm "idleAll"
    , goldenPlcFromPirCatch pTerm "some"
    , goldenEvalPir pTerm "listMatchEval"
    , goldenTypeFromPir topSrcSpan pTerm "dataEscape"
    ]

recursion :: TestNested
recursion = testNested "recursion"
    [ goldenNamedUPlcFromPir pTerm "factorial"
    , goldenPlcFromPir pTerm "even3"
    , goldenEvalPir pTerm "even3Eval"
    , goldenPlcFromPir pTerm "stupidZero"
    , goldenPlcFromPir pTerm "mutuallyRecursiveValues"
    , goldenEvalPir pTerm "errorBinding"
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
    [ goldenPlcFromPirCatch pTerm "mutuallyRecursiveTypes"
    , goldenPlcFromPirCatch pTerm "recursiveTypeBind"
    ]
