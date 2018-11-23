{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import           Common
import           PlcTestUtils

import           Language.PlutusCore.Quote

import           Language.PlutusIR
import           Language.PlutusIR.Compiler

import qualified Language.PlutusCore                  as PLC
import qualified Language.PlutusCore.MkPlc            as PLC
import qualified Language.PlutusCore.Pretty           as PLC

import qualified Language.PlutusCore.StdLib.Data.Bool as Bool
import qualified Language.PlutusCore.StdLib.Data.Nat  as Nat
import qualified Language.PlutusCore.StdLib.Data.Unit as Unit
import qualified Language.PlutusCore.StdLib.Meta      as Meta
import           Language.PlutusCore.StdLib.Type

import           Test.Tasty

import           Codec.Serialise
import           Control.Monad
import           Control.Monad.Except

import           Data.ByteString.Lazy                 as BSL

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

instance GetProgram (Quote (Term TyName Name ())) where
    getProgram = trivialProgram . compileAndMaybeTypecheck False

goldenPir :: String -> Term TyName Name () -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ prettyDef value

compileAndMaybeTypecheck :: Bool -> Quote (Term TyName Name ()) -> PLC.Term TyName Name ()
compileAndMaybeTypecheck doTypecheck pir = either (error . show . PLC.prettyPlcClassicDebug) id $ runExcept $ runQuoteT $ do
    -- it is important we run the two computations in the same Quote together, otherwise we might make
    -- names during compilation that are not fresh
    compiled <- compileTerm =<< liftQuote pir
    when doTypecheck $ void $
        convertErrors PLCError $ do
            annotated <- PLC.annotateTerm compiled
            -- need our own typechecker pipeline to allow normalized types
            PLC.typecheckTerm (PLC.TypeCheckCfg PLC.defaultTypecheckerGas $ PLC.TypeConfig True mempty) annotated
    pure compiled

compile :: Quote (Term TyName Name ()) -> PLC.Term TyName Name ()
compile = compileAndMaybeTypecheck True

tests :: TestNested
tests = testGroup "plutus-ir" <$> sequence [
    prettyprinting,
    datatypes,
    recursion,
    serialization
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
    m <- freshTyName () "Maybe"
    a <- freshTyName () "a"
    match <- freshName () "match_Maybe"
    nothing <- freshName () "Nothing"
    just <- freshName () "Just"
    unit <- Unit.getBuiltinUnit
    unitval <- embedIntoIR <$> Unit.getBuiltinUnitval
    pure $
        Let ()
            NonRec
            ([
                DatatypeBind () $
                Datatype ()
                    (TyVarDecl () m (KindArrow () (Type ()) (Type ())))
                    [
                        TyVarDecl () a (Type ())
                    ]
                match
                [
                    VarDecl () nothing (TyApp () (TyVar () m) (TyVar () a)),
                    VarDecl () just (TyFun () (TyVar () a) (TyApp () (TyVar () m) (TyVar () a)))
                ]
             ]) $
        Apply () (TyInst () (Var () just) unit) unitval

listMatch :: Quote (Term TyName Name ())
listMatch = do
    m <- freshTyName () "List"
    a <- freshTyName () "a"
    let ma = TyApp () (TyVar () m) (TyVar () a)
    match <- freshName () "match_List"
    nil <- freshName () "Nil"
    cons <- freshName () "Cons"
    unit <- Unit.getBuiltinUnit
    unitval <- Unit.getBuiltinUnitval

    h <- freshName () "head"
    t <- freshName () "tail"

    let unitMatch = PLC.TyInst () (PLC.Var () match) unit
    let unitNil = PLC.TyInst () (PLC.Var () nil) unit
    pure $
        Let ()
            Rec
            ([
                DatatypeBind () $
                Datatype ()
                    (TyVarDecl () m (KindArrow () (Type ()) (Type ())))
                    [
                        TyVarDecl () a (Type ())
                    ]
                match
                [
                    VarDecl () nil ma,
                    VarDecl () cons (TyFun () (TyVar () a) (TyFun () ma ma))
                ]
             ]) $
            -- embed so we can use PLC construction functions
            embedIntoIR $ PLC.mkIterApp () (PLC.TyInst () (PLC.Apply () unitMatch unitNil) unit)
                [
                    -- nil case
                    unitval,
                    -- cons case
                    PLC.mkIterLamAbs () [PLC.VarDecl () h unit, PLC.VarDecl () t (PLC.TyApp () (PLC.TyVar () m) unit)] $ PLC.Var () h
                ]

datatypes :: TestNested
datatypes = testNested "datatypes" [
    goldenPlc "maybe" (compile maybePir),
    goldenPlc "listMatch" (compileAndMaybeTypecheck False listMatch),
    goldenEval "listMatchEval" [listMatch]
    ]

recursion :: TestNested
recursion = testNested "recursion" [
    goldenPlc "even3" (compile evenOdd),
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
            ([
                TermBind () (VarDecl () arg nat) three
             ]) $
        Let ()
            Rec
            ([
                TermBind () (VarDecl () evenn evenTy) evenF,
                TermBind () (VarDecl () oddd oddTy) oddF
             ]) $
        Apply () (Var () evenn) (Var () arg)

serialization :: TestNested
serialization = testNested "serialization" [
    goldenPir "serializeBasic" (roundTripPirTerm basic),
    goldenPir "serializeMaybePirTerm" (roundTripPirTerm $ runQuote maybePir),
    goldenPir "serializeEvenOdd" (roundTripPirTerm $ runQuote evenOdd),
    goldenPir "serializeListMatch" (roundTripPirTerm $ runQuote listMatch)
    ]

roundTripPirTerm :: Term TyName Name () -> Term TyName Name ()
roundTripPirTerm tt = deserialise $ serialise tt
