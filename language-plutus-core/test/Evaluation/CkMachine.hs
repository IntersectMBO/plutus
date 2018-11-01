{-# LANGUAGE OverloadedStrings #-}
module Evaluation.CkMachine
    ( test_evaluateCk
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.CkMachine
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Generators.Test
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Type

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                       as BSL
import           Data.List
import           Data.Text.Encoding                         (encodeUtf8)
import           System.FilePath                            ((</>))
import           Test.Tasty
import           Test.Tasty.Golden
import           Test.Tasty.Hedgehog

natToBool :: Quote (Type TyName ())
natToBool = do
    RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat
    TyFun () nat <$> getBuiltinBool

evenAndOdd :: Quote (Term TyName Name ())
evenAndOdd = do
    RecursiveType _ nat1 <- holedToRecursive <$> getBuiltinNat
    b1 <- getBuiltinBool
    RecursiveType _ nat2 <- holedToRecursive <$> getBuiltinNat
    b2 <- getBuiltinBool

    true <- getBuiltinTrue
    false <- getBuiltinFalse

    fix2 <- getBuiltinFixN 2

    q <- freshTyName () "Q"

    choose <- freshName () "choose"
    chooseTy <- do
        ntb1 <- natToBool
        ntb2 <- natToBool
        pure $ TyFun () ntb1 (TyFun () ntb2 (TyVar () q))

    evenn <- freshName () "even"
    evenTy <- natToBool
    oddd <- freshName () "odd"
    oddTy <- natToBool

    let eoFunc b recc = do
          n <- freshName () "n"
          RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat
          bool <- getBuiltinBool
          pure $
              LamAbs () n nat $
              Apply () (Apply () (TyInst () (Unwrap () (Var () n)) bool) b) $ Var () recc

    evenF <- eoFunc true oddd
    oddF <- eoFunc false evenn

    pure $
        Apply () (foldl' (\acc t -> TyInst () acc t) fix2 [nat1, b1, nat2, b2]) $
        TyAbs () q (Type ()) $
        LamAbs () choose chooseTy $
        LamAbs () evenn evenTy $
        LamAbs () oddd oddTy $
        Apply () (Apply () (Var () choose) evenF) oddF

getEven :: Quote (Term TyName Name ())
getEven = do
    both <- evenAndOdd
    instTy <- natToBool
    x <- freshName () "x"
    xTy <- natToBool
    y <- freshName () "y"
    yTy <- natToBool
    pure $
        Apply () (TyInst () both instTy) $
        LamAbs () x xTy $
        LamAbs () y yTy $
        Var () x

listInt :: Quote (Type TyName ())
listInt = do
    RecursiveType _ list1 <- holedToRecursive <$> getBuiltinList
    RecursiveType _ nat1 <- holedToRecursive <$> getBuiltinNat
    pure $ TyApp () list1 nat1

listIntToListInt :: Quote (Type TyName ())
listIntToListInt = TyFun () <$> listInt <*> listInt

evenAndOddList :: Quote (Term TyName Name ())
evenAndOddList = do
    fix2 <- getBuiltinFixN 2

    q <- freshTyName () "Q"

    choose <- freshName () "choose"
    chooseTy <- do
        li1 <- listIntToListInt
        li2 <- listIntToListInt
        pure $ TyFun () li1 (TyFun () li2 (TyVar () q))

    evenn <- freshName () "even"
    evenTy <- listIntToListInt
    oddd <- freshName () "odd"
    oddTy <- listIntToListInt

    let eoFunc recc = do
          l <- freshName () "l"
          li1 <- listInt
          li2 <- listInt

          nil <- getBuiltinNil
          RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat

          pure $
              LamAbs () l li1 $
              Apply () (
                  Apply () (TyInst () (Unwrap () (Var () l)) li2)
                  (TyInst() nil nat))
              recc

    evenF <- do
        h <- freshName () "head"
        RecursiveType _ nat1 <- holedToRecursive <$> getBuiltinNat
        t <- freshName () "tail"
        li1 <- listInt
        cons <- getBuiltinCons
        RecursiveType _ nat2 <- holedToRecursive <$> getBuiltinNat
        eoFunc $
            LamAbs () h nat1 $
            LamAbs () t li1 $
            Apply () (Apply () (TyInst () cons nat2) (Var () h)) $
            Apply () (Var () oddd) (Var () t)

    oddF <- do
        h <- freshName () "head"
        RecursiveType _ nat1 <- holedToRecursive <$> getBuiltinNat
        t <- freshName () "tail"
        li1 <- listInt
        eoFunc $
            LamAbs () h nat1 $
            LamAbs () t li1 $
            Apply () (Var () evenn) (Var () t)

    lis <- replicateM 4 listInt
    pure $
        Apply () (foldl' (\acc t -> TyInst () acc t) fix2 lis) $
        TyAbs () q (Type ()) $
        LamAbs () choose chooseTy $
        LamAbs () evenn evenTy $
        LamAbs () oddd oddTy $
        Apply () (Apply () (Var () choose) evenF) oddF

getEvenList :: Quote (Term TyName Name ())
getEvenList = do
    both <- evenAndOddList
    instTy <- listIntToListInt
    x <- freshName () "x"
    xTy <- listIntToListInt
    y <- freshName () "y"
    yTy <- listIntToListInt
    pure $
        Apply () (TyInst () both instTy) $
        LamAbs () x xTy $
        LamAbs () y yTy $
        Var () x

smallNatList :: Quote (Term TyName Name ())
smallNatList = do
    nats <- mapM getBuiltinIntegerToNat [1,2,3]
    RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat
    getListToBuiltinList nat nats

goldenVsPretty :: PrettyPlc a => FilePath -> String -> ExceptT BSL.ByteString IO a -> TestTree
goldenVsPretty testDir name value = goldenVsString name (testDir </> "test/Evaluation/" ++ name ++ ".plc.golden") $ either id (BSL.fromStrict . encodeUtf8 . docText . prettyPlcClassicDebug) <$> runExceptT value

test_evaluateCk :: FilePath -> TestTree
test_evaluateCk testDir = testGroup "evaluateCk"
    [ testGroup "props" $ fromInterestingTermGens (\name -> testProperty name . propEvaluate evaluateCk)
    , goldenVsPretty testDir "even2" (pure $ evaluateCk (runQuote $
                                                 Apply () <$> getEven <*> getBuiltinIntegerToNat 2))
    , goldenVsPretty testDir "even3" (pure $ evaluateCk (runQuote $
                                                 Apply () <$> getEven <*> getBuiltinIntegerToNat 3))
    , goldenVsPretty testDir "evenList" (pure $ evaluateCk (runQuote $
                                                 Apply () <$> getBuiltinNatSum 64 <*> (Apply () <$> getEvenList <*> smallNatList)))
    ]
