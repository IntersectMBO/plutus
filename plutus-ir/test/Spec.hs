{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import           Common
import           PlutusPrelude                            (bsToStr, strToBs)

import           Language.PlutusCore.Quote

import           Language.PlutusIR
import           Language.PlutusIR.Compiler

import qualified Language.PlutusCore                      as PLC
import qualified Language.PlutusCore.Evaluation.CkMachine as PLC
import qualified Language.PlutusCore.Pretty               as PLC

import qualified Language.PlutusCore.StdLib.Data.Bool     as Bool
import qualified Language.PlutusCore.StdLib.Data.Nat      as Nat
import qualified Language.PlutusCore.StdLib.Data.Unit     as Unit
import qualified Language.PlutusCore.StdLib.Meta          as Meta
import           Language.PlutusCore.StdLib.Type

import           Control.Monad.Except

import           Test.Tasty

import qualified Data.ByteString.Lazy                     as BSL
import qualified Data.Text.Prettyprint.Doc                as PP

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

-- TODO: share more code with plugin testing lib
class GetProgram a where
    getProgram :: a -> ExceptT BSL.ByteString IO (PLC.Program TyName Name ())

instance GetProgram (PLC.Program TyName Name ()) where
    getProgram = pure

instance GetProgram (PLC.Term TyName Name ()) where
    getProgram = pure . trivialProgram

instance GetProgram (Term TyName Name ()) where
    getProgram = pure . trivialProgram . compile

trivialProgram :: PLC.Term TyName Name () -> PLC.Program TyName Name ()
trivialProgram = PLC.Program () (PLC.defaultVersion ())

runPlc :: (GetProgram a) => [a] -> ExceptT BSL.ByteString IO PLC.EvaluationResult
runPlc values = do
    ps <- mapM getProgram values
    let p = foldl1 (\acc p -> PLC.applyProgram acc p) ps
    pure $ PLC.runCk p

goldenPIR :: String -> Term TyName Name () -> TestNested
goldenPIR name value = nestedGoldenVsDoc name $ prettyDef value

goldenPLC :: String -> PLC.Term TyName Name () -> TestNested
goldenPLC name value = nestedGoldenVsDoc name $ PLC.prettyPlcDef value

goldenEval :: (GetProgram a) => String -> [a] -> TestNested
goldenEval name values = nestedGoldenVsDocM name $ either (PP.pretty . bsToStr) PLC.prettyPlcClassicDebug <$> (runExceptT $ runPlc values)

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
    goldenPIR "basic" basic
    , goldenPIR "datatype" datatype
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
    goldenPLC "maybe" (compile datatype)
    ]

recursion :: TestNested
recursion = testNested "recursion" [
    goldenPLC "even3" (compile evenOdd),
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
