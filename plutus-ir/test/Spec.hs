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

import qualified Language.PlutusCore.StdLib.Data.Bool as Bool
import qualified Language.PlutusCore.StdLib.Data.Nat  as Nat
import qualified Language.PlutusCore.StdLib.Data.Unit as Unit
import qualified Language.PlutusCore.StdLib.Meta      as Meta
import           Language.PlutusCore.StdLib.Type

import           Test.Tasty

import qualified Data.Text.Prettyprint.Doc            as PP

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

instance GetProgram (Term TyName Name ()) where
    getProgram = trivialProgram . compile

goldenPir :: String -> Term TyName Name () -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ prettyDef value

compile :: Term TyName Name () -> PLC.Term TyName Name ()
compile pir = case runCompiling $ compileTerm pir of
    Right plc -> plc
    Left e    -> error (show $ PP.pretty e)

tests :: TestNested
tests = testGroup "plutus-ir" <$> sequence [
    prettyprinting,
    datatypes,
    recursion
    ]

prettyprinting :: TestNested
prettyprinting = testNested "prettyprinting" [
    goldenPir "basic" basic
    , goldenPir "datatype" datatype
    ]

basic :: Term TyName Name ()
basic = runQuote $ do
    a <- freshTyName () "a"
    x <- freshName () "x"
    pure $
        TyAbs () a (Type ()) $
        LamAbs () x (TyVar () a) $
        Var () x

datatype :: Term TyName Name ()
datatype = runQuote $ do
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
            [
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
            ] $
        Apply () (TyInst () (Var () just) unit) unitval

datatypes :: TestNested
datatypes = testNested "datatypes" [
    goldenPlc "maybe" (compile datatype)
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

evenOdd :: Term TyName Name ()
evenOdd = runQuote $ do
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
