{-# LANGUAGE OverloadedStrings #-}
module Evaluation.CkMachine
    ( test_evaluateCk
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.CkMachine
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Generators.Test
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                       as BSL
import           Data.Text.Encoding                         (encodeUtf8)
import           Test.Tasty
import           Test.Tasty.Golden
import           Test.Tasty.Hedgehog

getEvenAndOdd :: Quote (Tuple ())
getEvenAndOdd = do
    nat  <- _recursiveType <$> getBuiltinNat
    bool <- getBuiltinBool

    true  <- getBuiltinTrue
    false <- getBuiltinFalse

    evenn <- freshName () "even"
    oddd  <- freshName () "odd"

    let eoFunc b recc = do
          n <- freshName () "n"
          pure $
              LamAbs () n nat $
              Apply () (Apply () (TyInst () (Unwrap () (Var () n)) bool) b) $ Var () recc

    evenF <- FunctionDef () evenn (FunctionType () nat bool) <$> eoFunc true oddd
    oddF  <- FunctionDef () oddd  (FunctionType () nat bool) <$> eoFunc false evenn

    getBuiltinMutualFixOf () [evenF, oddF]

getEven :: Quote (Term TyName Name ())
getEven = getEvenAndOdd >>= tupleTermAt () 0

getEvenAndOddList :: Quote (Tuple ())
getEvenAndOddList = do
    list <- _recursiveType <$> getBuiltinList
    nat  <- _recursiveType <$> getBuiltinNat
    let listNat = TyApp () list nat

    nil  <- getBuiltinNil
    cons <- getBuiltinCons

    evenn <- freshName () "even"
    oddd  <- freshName () "odd"

    let eoFunc recc = do
          l <- freshName () "l"
          pure $
              LamAbs () l listNat $
              Apply () (
                  Apply () (TyInst () (Unwrap () (Var () l)) listNat)
                  (TyInst() nil nat))
              recc

    evenF <- FunctionDef () evenn (FunctionType () listNat listNat) <$> do
        h <- freshName () "head"
        t <- freshName () "tail"
        eoFunc $
            LamAbs () h nat $
            LamAbs () t listNat $
            Apply () (Apply () (TyInst () cons nat) (Var () h)) $
            Apply () (Var () oddd) (Var () t)

    oddF <- FunctionDef () oddd (FunctionType () listNat listNat) <$> do
        h <- freshName () "head"
        t <- freshName () "tail"
        eoFunc $
            LamAbs () h nat $
            LamAbs () t listNat $
            Apply () (Var () evenn) (Var () t)

    getBuiltinMutualFixOf () [evenF, oddF]

getEvenList :: Quote (Term TyName Name ())
getEvenList = getEvenAndOddList >>= tupleTermAt () 0

smallNatList :: Quote (Term TyName Name ())
smallNatList = do
    nats <- mapM getBuiltinIntegerToNat [1,2,3]
    nat <- _recursiveType <$> getBuiltinNat
    getListToBuiltinList nat nats

goldenVsPretty :: PrettyPlc a => String -> ExceptT BSL.ByteString IO a -> TestTree
goldenVsPretty name value = goldenVsString name ("test/Evaluation/" ++ name ++ ".plc.golden") $ either id (BSL.fromStrict . encodeUtf8 . docText . prettyPlcClassicDebug) <$> runExceptT value

test_evaluateCk :: TestTree
test_evaluateCk = testGroup "evaluateCk"
    [ testGroup "props" $ fromInterestingTermGens (\name -> testProperty name . propEvaluate evaluateCk)
    , goldenVsPretty "even2" (pure $ evaluateCk (runQuote $
                                                 Apply () <$> getEven <*> getBuiltinIntegerToNat 2))
    , goldenVsPretty "even3" (pure $ evaluateCk (runQuote $
                                                 Apply () <$> getEven <*> getBuiltinIntegerToNat 3))
    , goldenVsPretty "evenList" (pure $ evaluateCk (runQuote $
                                                 Apply () <$> getBuiltinNatSum 64 <*> (Apply () <$> getEvenList <*> smallNatList)))
    ]
