{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import           Common
import           PlcTestUtils
import           PlutusPrelude              hiding (hoist)
import           TestLib

import           OptimizerSpec
import           ParserSpec
import           TransformSpec

import           Language.PlutusCore.Quote

import           Language.PlutusIR
import           Language.PlutusIR.Compiler
import           Language.PlutusIR.Parser   hiding (Error)

import qualified Language.PlutusCore        as PLC

import           Test.Tasty

import           Codec.Serialise
import           Control.Exception
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Morph
import           Control.Monad.Reader

import           Data.Functor.Identity

import           Text.Megaparsec.Pos

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

instance (Pretty a, Typeable a) => GetProgram (Term TyName Name a) where
    getProgram = asIfThrown . fmap (trivialProgram . void) . compileAndMaybeTypecheck True

instance Pretty SourcePos where
    pretty = pretty . sourcePosPretty

-- | Adapt an computation that keeps its errors in an 'Except' into one that looks as if it caught them in 'IO'.
asIfThrown
    :: Exception e
    => Except e a
    -> ExceptT SomeException IO a
asIfThrown = withExceptT SomeException . hoist (pure . runIdentity)

compileAndMaybeTypecheck :: Bool -> Term TyName Name a -> Except (Error (Provenance a)) (PLC.Term TyName Name (Provenance a))
compileAndMaybeTypecheck doTypecheck pir = flip runReaderT NoProvenance $ runQuoteT $ do
    compiled <- compileTerm pir
    when doTypecheck $ void $ PLC.inferType PLC.defOffChainConfig compiled
    pure compiled

tests :: TestNested
tests = testGroup "plutus-ir" <$> sequence
    [ prettyprinting
    , parsing
    , datatypes
    , recursion
    , serialization
    , errors
    , optimizer
    , transform
    ]

prettyprinting :: TestNested
prettyprinting = testNested "prettyprinting"
    $ map (goldenPir id term)
    [ "basic"
    , "maybe"
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

roundTripPirTerm :: Term TyName Name a -> Term TyName Name ()
roundTripPirTerm = deserialise . serialise . void

errors :: TestNested
errors = testNested "errors"
    [ goldenPlcFromPirCatch term "mutuallyRecursiveTypes"
    ]
