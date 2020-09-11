{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import           Common
import           PlcTestUtils
import           PlutusPrelude
import           TestLib

import           OptimizerSpec
import           ParserSpec
import           TransformSpec
import           TypeSpec

import           Language.PlutusCore.Pretty (PrettyConst)
import           Language.PlutusCore.Quote

import           Language.PlutusIR
import           Language.PlutusIR.Compiler
import           Language.PlutusIR.Parser   hiding (Error)

import qualified Language.PlutusCore        as PLC

import           Test.Tasty

import           Codec.Serialise
import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Morph
import           Control.Monad.Reader
import Control.Lens hiding (transform)

main :: IO ()
main = defaultMain $ runTestNestedIn ["plutus-ir-test"] tests

instance ( PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni
         , PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, Pretty a, Typeable a, Typeable uni, Ord a
         ) => GetProgram (Term TyName Name uni a) uni where
    getProgram = asIfThrown . fmap (trivialProgram . void) . compileAndMaybeTypecheck True

-- | Adapt an computation that keeps its errors in an 'Except' into one that looks as if it caught them in 'IO'.
asIfThrown
    :: Exception e
    => Except e a
    -> ExceptT SomeException IO a
asIfThrown = withExceptT SomeException . hoist (pure . runIdentity)

compileAndMaybeTypecheck
    :: (PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni, Ord a)
    => Bool
    -> Term TyName Name uni a
    -> Except (Error uni (Provenance a)) (PLC.Term TyName Name uni (Provenance a))
compileAndMaybeTypecheck doTypecheck pir = flip runReaderT defaultCompilationCtx $ runQuoteT $ do
    compiled <- compileTerm doTypecheck pir
    when doTypecheck $ do
        -- PLC errors are parameterized over PLC.Terms, whereas PIR errors over PIR.Terms and as such, these prism errors cannot be unified.
        -- We instead run the ExceptT, collect any PLC error and explicitly lift into a PIR error by wrapping with PIR._PLCError
        plcConcrete <- runExceptT $ void $ PLC.inferType PLC.defConfig compiled
        liftEither $ first (view (re _PLCError)) plcConcrete
    pure compiled

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

roundTripPirTerm :: Term TyName Name PLC.DefaultUni a -> Term TyName Name PLC.DefaultUni ()
roundTripPirTerm = deserialise . serialise . void

errors :: TestNested
errors = testNested "errors"
    [ goldenPlcFromPirCatch term "mutuallyRecursiveTypes"
    , goldenPlcFromPirCatch term "recursiveTypeBind"
    ]
