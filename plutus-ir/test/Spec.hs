{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Common

import           Language.PlutusCore.Quote
import           Language.PlutusIR

import           Language.PlutusCore.StdLib.Data.Unit as Unit

import           Test.Tasty

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

golden :: String -> Term TyName Name () -> TestNested
golden name value = nestedGoldenVsDoc name $ prettyDef value

tests :: TestNested
tests = testGroup "plutus-ir" <$> sequence [
    basicTests
    ]

basicTests :: TestNested
basicTests = testNested "prettyprinting" [
    golden "basic" basic
    , golden "datatype" datatype
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
    unit <- getBuiltinUnit
    unitval <- embedIntoIR <$> getBuiltinUnitval
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
