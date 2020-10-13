{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import           Common
import           PlutusPrelude
import           TestLib

import           OptimizerSpec
import           ParserSpec
import           TransformSpec
import           TypeSpec

import           Language.PlutusIR
import           Language.PlutusIR.Parser hiding (Error)

import qualified Language.PlutusCore      as PLC

import           Test.Tasty

import           Codec.Serialise

main :: IO ()
main = defaultMain $ runTestNestedIn ["plutus-ir-test"] tests

tests :: TestNested
tests = testGroup "plutus-ir" <$> sequence
    [ prettyprinting
    , parsing
    , lets
    , datatypes
    , recursion
    , serialization
    , errors
    , optimizer
    , transform
    , types
    , typeErrors
    ]

prettyprinting :: TestNested
prettyprinting = testNested "prettyprinting"
    $ map (goldenPir id term)
    [ "basic"
    , "maybe"
    ]

lets :: TestNested
lets = testNested "lets"
    [ goldenPlcFromPir term "letInLet"
    , goldenPlcFromPir term "letDep"
    ]

datatypes :: TestNested
datatypes = testNested "datatypes"
    [ goldenPlcFromPir term "maybe"
    , goldenPlcFromPir term "listMatch"
    , goldenEvalPir term "listMatchEval"
    ]

recursion :: TestNested
recursion = testNested "recursion"
    [ goldenPlcFromPir term "even3"
    , goldenEvalPir term "even3Eval"
    , goldenPlcFromPir term "stupidZero"
    , goldenPlcFromPir term "mutuallyRecursiveValues"
    ]

serialization :: TestNested
serialization = testNested "serialization"
    $ map (goldenPir roundTripPirTerm term)
    [ "serializeBasic"
    , "serializeMaybePirTerm"
    , "serializeEvenOdd"
    , "serializeListMatch"
    ]

roundTripPirTerm :: Term TyName Name PLC.DefaultUni PLC.DefaultFun a -> Term TyName Name PLC.DefaultUni PLC.DefaultFun ()
roundTripPirTerm = deserialise . serialise . void

errors :: TestNested
errors = testNested "errors"
    [ goldenPlcFromPirCatch term "mutuallyRecursiveTypes"
    , goldenPlcFromPirCatch term "recursiveTypeBind"
    ]
