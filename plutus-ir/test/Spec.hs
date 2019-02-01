{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import           Common
import           PlcTestUtils
import           TestLib

import           OptimizerSpec
import           TransformSpec

import           Language.PlutusCore.Quote

import           Language.PlutusIR
import           Language.PlutusIR.Compiler
import           Language.PlutusIR.MkPir

import qualified Language.PlutusCore                  as PLC

import qualified Language.PlutusCore.StdLib.Data.Bool as Bool
import qualified Language.PlutusCore.StdLib.Data.Nat  as Nat
import qualified Language.PlutusCore.StdLib.Data.Unit as Unit
import qualified Language.PlutusCore.StdLib.Meta      as Meta
import           Language.PlutusCore.StdLib.Type

import           Test.Tasty

import           Codec.Serialise
import           Control.Exception
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Morph
import           Control.Monad.Reader

import           Data.Functor.Identity

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

instance GetProgram (Term TyName Name ()) where
    getProgram = asIfThrown . fmap (trivialProgram . void) . compileAndMaybeTypecheck True

-- | Adapt an computation that keeps its errors in an 'Except' into one that looks as if it caught them in 'IO'.
asIfThrown
    :: Exception e
    => Except e a
    -> ExceptT SomeException IO a
asIfThrown = withExceptT SomeException . hoist (pure . runIdentity)

compileAndMaybeTypecheck :: Bool -> Term TyName Name a -> Except (Error (Provenance a)) (PLC.Term TyName Name (Provenance a))
compileAndMaybeTypecheck doTypecheck pir = flip runReaderT NoProvenance $ runQuoteT $ do
    -- it is important we run the two computations in the same Quote together, otherwise we might make
    -- names during compilation that are not fresh
    compiled <- compileTerm pir -- =<< PLC.rename pir
    when doTypecheck $ void $ PLC.inferType PLC.defOffChainConfig compiled
    pure compiled

tests :: TestNested
tests = testGroup "plutus-ir" <$> sequence [
    prettyprinting,
    datatypes,
    recursion,
    serialization,
    errors,
    optimizer,
    transform
    ]

prettyprinting :: TestNested
prettyprinting = testNested "prettyprinting" [
    goldenPir "basic" basic
    , goldenPir "maybe" maybePir
    ]

basic :: Term TyName Name ()
basic = runQuote $ do
    a <- freshTyName () "a"
    x <- freshName () "x"
    pure $
        TyAbs () a (Type ()) $
        LamAbs () x (TyVar () a) $
        Var () x

maybePir :: Term TyName Name ()
maybePir = runQuote $ do
    mb@(Datatype _ _ _ _ [_, just]) <- maybeDatatype
    let unitval = embedIntoIR Unit.unitval
    pure $
        Let ()
            NonRec
            [
                DatatypeBind () mb
            ] $
        Apply () (TyInst () (mkVar () just) Unit.unit) unitval

listMatch :: Term TyName Name ()
listMatch = runQuote $ do
    lb@(Datatype _ l _ match [nil, _]) <- listDatatype

    let unitval = embedIntoIR Unit.unitval

    h <- freshName () "head"
    t <- freshName () "tail"

    let unitMatch = TyInst () (Var () match) Unit.unit
    let unitNil = TyInst () (mkVar () nil) Unit.unit

    pure $
        Let ()
            Rec
            [
                DatatypeBind () lb
            ] $
            mkIterApp () (TyInst () (Apply () unitMatch unitNil) Unit.unit)
                [
                    -- nil case
                    unitval,
                    -- cons case
                    mkIterLamAbs () [VarDecl () h Unit.unit, VarDecl () t (TyApp () (mkTyVar () l) Unit.unit)] $ Var () h
                ]

datatypes :: TestNested
datatypes = testNested "datatypes" [
    goldenPlc "maybe" maybePir,
    goldenPlc "listMatch" listMatch,
    goldenEval "listMatchEval" [listMatch]
    ]

recursion :: TestNested
recursion = testNested "recursion" [
    goldenPlc "even3" evenOdd,
    goldenEval "even3Eval" [evenOdd],
    goldenPlc "mutuallyRecursiveValues" mutuallyRecursiveValues
    ]

natToBool :: Type TyName ()
natToBool =
    let nat = _recursiveType Nat.natData
    in TyFun () nat Bool.bool

evenOdd :: Term TyName Name ()
evenOdd = runQuote $ do
    let true = embedIntoIR Bool.true
        false = embedIntoIR Bool.false
        nat = _recursiveType Nat.natData

    evenn <- freshName () "even"
    oddd <- freshName () "odd"

    let eoFunc b recc = do
          n <- freshName () "n"
          pure $
              LamAbs () n nat $
              Apply () (Apply () (TyInst () (Unwrap () (Var () n)) Bool.bool) b) $ Var () recc

    evenF <- eoFunc true oddd
    oddF <- eoFunc false evenn

    arg <- freshName () "arg"
    let three = embedIntoIR $ Meta.metaIntegerToNat 3
    pure $
        Let ()
            NonRec
            [
                TermBind () (VarDecl () arg nat) three
            ] $
        Let ()
            Rec
            [
                TermBind () (VarDecl () evenn natToBool) evenF,
                TermBind () (VarDecl () oddd natToBool) oddF
            ] $
        Apply () (Var () evenn) (Var () arg)

mutuallyRecursiveValues :: Term TyName Name ()
mutuallyRecursiveValues = runQuote $ do
    x <- freshName () "x"
    y <- freshName () "y"

    let unitval = embedIntoIR Unit.unitval

    pure $
        Let ()
            Rec
            [
                TermBind () (VarDecl () x Unit.unit) (Var () y),
                TermBind () (VarDecl () y Unit.unit) unitval
            ] $
        Var () x

serialization :: TestNested
serialization = testNested "serialization" [
    goldenPir "serializeBasic" (roundTripPirTerm basic),
    goldenPir "serializeMaybePirTerm" (roundTripPirTerm maybePir),
    goldenPir "serializeEvenOdd" (roundTripPirTerm evenOdd),
    goldenPir "serializeListMatch" (roundTripPirTerm listMatch)
    ]

roundTripPirTerm :: Term TyName Name () -> Term TyName Name ()
roundTripPirTerm tt = deserialise $ serialise tt

errors :: TestNested
errors = testNested "errors" [
    goldenPlcCatch "mutuallyRecursiveTypes" mutuallyRecursiveTypes
    ]

mutuallyRecursiveTypes :: Term TyName Name ()
mutuallyRecursiveTypes = runQuote $ do
    (treeDt, forestDt@(Datatype _ _ _ _ [nil, _])) <- treeForestDatatype
    pure $
        Let ()
            Rec
            [
                DatatypeBind () treeDt,
                DatatypeBind () forestDt
            ] $
        TyInst () (mkVar () nil) Unit.unit
