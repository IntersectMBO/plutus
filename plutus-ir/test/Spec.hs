{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import qualified Bazel.Runfiles                       as Runfiles
import           Common
import           PlcTestUtils
import           TestLib

import           OptimizerSpec

import           Language.PlutusCore.Quote

import           Language.PlutusIR
import           Language.PlutusIR.Compiler
import           Language.PlutusIR.MkPir

import qualified Language.PlutusCore                  as PLC
import qualified Language.PlutusCore.MkPlc            as PLC

import qualified Language.PlutusCore.StdLib.Data.Bool as Bool
import qualified Language.PlutusCore.StdLib.Data.Nat  as Nat
import qualified Language.PlutusCore.StdLib.Data.Unit as Unit
import qualified Language.PlutusCore.StdLib.Meta      as Meta
import           Language.PlutusCore.StdLib.Type

import           Test.Tasty

import           Control.Exception
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Morph
import           Control.Monad.Reader

import           Data.Functor.Identity

main :: IO ()
main = do
    mr <- Runfiles.createMaybe
    let testDir = case mr of
          Just r  -> Runfiles.rlocation r "plutus/plutus-ir/"
          Nothing -> "."
    defaultMain $ runTestNestedIn [testDir, "test"] tests

instance GetProgram (Quote (Term TyName Name ())) where
    getProgram = asIfThrown . fmap (trivialProgram . void) . compileAndMaybeTypecheck True

-- | Adapt an computation that keeps its errors in an 'Except' into one that looks as if it caught them in 'IO'.
asIfThrown
    :: Exception e
    => Except e a
    -> ExceptT SomeException IO a
asIfThrown = withExceptT SomeException . hoist (pure . runIdentity)

compileAndMaybeTypecheck :: Bool -> Quote (Term TyName Name a) -> Except (Error (Provenance a)) (PLC.Term TyName Name (Provenance a))
compileAndMaybeTypecheck doTypecheck pir = flip runReaderT NoProvenance $ runQuoteT $ do
    -- it is important we run the two computations in the same Quote together, otherwise we might make
    -- names during compilation that are not fresh
    compiled <- compileTerm =<< liftQuote pir
    when doTypecheck $ void $ do
        annotated <- PLC.annotateTerm compiled
        -- need our own typechecker pipeline to allow normalized types
        PLC.typecheckTerm (PLC.TypeCheckCfg PLC.defaultTypecheckerGas $ PLC.TypeConfig True mempty) annotated
    pure compiled

tests :: TestNested
tests = testGroup "plutus-ir" <$> sequence [
    prettyprinting,
    datatypes,
    recursion,
    errors,
    optimizer
    ]

prettyprinting :: TestNested
prettyprinting = testNested "prettyprinting" [
    goldenPir "basic" basic
    , goldenPir "maybe" (runQuote maybePir)
    ]

basic :: Term TyName Name ()
basic = runQuote $ do
    a <- freshTyName () "a"
    x <- freshName () "x"
    pure $
        TyAbs () a (Type ()) $
        LamAbs () x (TyVar () a) $
        Var () x

maybePir :: Quote (Term TyName Name ())
maybePir = do
    mb@(Datatype _ _ _ _ [_, just]) <- maybeDatatype

    unit <- Unit.getBuiltinUnit
    unitval <- embedIntoIR <$> Unit.getBuiltinUnitval

    pure $
        Let ()
            NonRec
            [
                DatatypeBind () mb
            ] $
        Apply () (TyInst () (mkVar () just) unit) unitval

listMatch :: Quote (Term TyName Name ())
listMatch = do
    lb@(Datatype _ l _ match [nil, _]) <- listDatatype

    unit <- Unit.getBuiltinUnit
    unitval <- embedIntoIR <$> Unit.getBuiltinUnitval

    h <- freshName () "head"
    t <- freshName () "tail"

    let unitMatch = TyInst () (Var () match) unit
    let unitNil = TyInst () (mkVar () nil) unit

    pure $
        Let ()
            Rec
            [
                DatatypeBind () lb
            ] $
            mkIterApp () (TyInst () (Apply () unitMatch unitNil) unit)
                [
                    -- nil case
                    unitval,
                    -- cons case
                    mkIterLamAbs () [VarDecl () h unit, VarDecl () t (TyApp () (mkTyVar () l) unit)] $ Var () h
                ]

datatypes :: TestNested
datatypes = testNested "datatypes" [
    goldenPlc "maybe" maybePir,
    goldenPlc "listMatch" (asIfThrown $ trivialProgram . void <$> compileAndMaybeTypecheck False listMatch),
    goldenEval "listMatchEval" [asIfThrown $ trivialProgram . void <$> compileAndMaybeTypecheck False listMatch]
    ]

recursion :: TestNested
recursion = testNested "recursion" [
    goldenPlc "even3" evenOdd,
    goldenEval "even3Eval" [evenOdd]
    ]

natToBool :: Quote (Type TyName ())
natToBool = do
    RecursiveType _ nat <- holedToRecursive <$> Nat.getBuiltinNat
    TyFun () nat <$> Bool.getBuiltinBool

evenOdd :: Quote (Term TyName Name ())
evenOdd = do
    true <- embedIntoIR <$> Bool.getBuiltinTrue
    false <- embedIntoIR <$> Bool.getBuiltinFalse

    evenn <- freshName () "even"
    evenTy <- natToBool
    oddd <- freshName () "odd"
    oddTy <- natToBool

    let eoFunc b recc = do
          n <- freshName () "n"
          RecursiveType _ nat <- holedToRecursive <$> Nat.getBuiltinNat
          bool <- Bool.getBuiltinBool
          pure $
              LamAbs () n nat $
              Apply () (Apply () (TyInst () (Unwrap () (Var () n)) bool) b) $ Var () recc

    evenF <- eoFunc true oddd
    oddF <- eoFunc false evenn

    arg <- freshName () "arg"
    RecursiveType _ nat <- holedToRecursive <$> Nat.getBuiltinNat
    three <- embedIntoIR <$> Meta.getBuiltinIntegerToNat 3
    pure $
        Let ()
            NonRec
            [
                TermBind () (VarDecl () arg nat) three
            ] $
        Let ()
            Rec
            [
                TermBind () (VarDecl () evenn evenTy) evenF,
                TermBind () (VarDecl () oddd oddTy) oddF
            ] $
        Apply () (Var () evenn) (Var () arg)

errors :: TestNested
errors = testNested "errors" [
    goldenPlcCatch "mutuallyRecursiveTypes" mutuallyRecursiveTypes,
    goldenPlcCatch "mutuallyRecursiveValues" mutuallyRecursiveValues
    ]

mutuallyRecursiveTypes :: Quote (Term TyName Name ())
mutuallyRecursiveTypes = do
    unit <- Unit.getBuiltinUnit

    (treeDt, forestDt@(Datatype _ _ _ _ [nil, _])) <- treeForestDatatype

    pure $
        Let ()
            Rec
            [
                DatatypeBind () treeDt,
                DatatypeBind () forestDt
            ] $
        TyInst () (mkVar () nil) unit

mutuallyRecursiveValues :: Quote (Term TyName Name ())
mutuallyRecursiveValues = do
    x <- freshName () "x"
    y <- freshName () "y"

    unit <- Unit.getBuiltinUnit
    unitval <- embedIntoIR <$> Unit.getBuiltinUnitval

    pure $
        Let ()
            Rec
            [
                TermBind () (VarDecl () x unit) (Var () y),
                TermBind () (VarDecl () y unit) unitval
            ] $
        Var () x
