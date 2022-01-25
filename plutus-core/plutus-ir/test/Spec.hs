{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import PlutusPrelude

import NamesSpec
import ParserSpec
import TransformSpec
import TypeSpec

import PlutusIR
import PlutusIR.Parser
import PlutusIR.Test

import PlutusCore qualified as PLC
import PlutusIR
import PlutusIR.Parser (pTerm)
import Test.Tasty
import Test.Tasty.Extras

import Flat (flat, unflat)

main :: IO ()
main = defaultMain $ runTestNestedIn ["plutus-ir/test"] tests

tests :: TestNested
tests = testGroup "plutus-ir" <$> sequence
    [ prettyprinting
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
    ]

prettyprinting :: TestNested
prettyprinting = testNested "prettyprinting"
    $ map (goldenPir id pTerm)
    [ "basic"
    , "maybe"
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
    ]

recursion :: TestNested
recursion = testNested "recursion"
    [ goldenPlcFromPir pTerm "even3"
    , goldenEvalPir pTerm "even3Eval"
    , goldenPlcFromPir pTerm "stupidZero"
    , goldenPlcFromPir pTerm "mutuallyRecursiveValues"
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
