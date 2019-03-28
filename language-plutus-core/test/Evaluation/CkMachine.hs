{-# LANGUAGE OverloadedStrings #-}
module Evaluation.CkMachine
    ( test_evaluateCk
    ) where

import           Prelude                                    hiding (even)

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

evenAndOdd :: Tuple ()
evenAndOdd = runQuote $ do
    let nat = _recursiveType natData

    evenn <- freshName () "even"
    oddd  <- freshName () "odd"

    let eoFunc b recc = do
          n <- freshName () "n"
          pure $
              LamAbs () n nat $
              Apply () (Apply () (TyInst () (Unwrap () (Var () n)) bool) b) $ Var () recc

    evenF <- FunctionDef () evenn (FunctionType () nat bool) <$> eoFunc true oddd
    oddF  <- FunctionDef () oddd  (FunctionType () nat bool) <$> eoFunc false evenn

    getMutualFixOf () [evenF, oddF]

even :: Term TyName Name ()
even = runQuote $ tupleTermAt () 0 evenAndOdd

evenAndOddList :: Tuple ()
evenAndOddList = runQuote $ do
    let list = _recursiveType listData
        nat  = _recursiveType natData
        listNat = TyApp () list nat

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

    getMutualFixOf () [evenF, oddF]

evenList :: Term TyName Name ()
evenList = runQuote $ tupleTermAt () 0 evenAndOddList

smallNatList :: Term TyName Name ()
smallNatList = metaListToList nat nats where
    nats = map metaIntegerToNat [1,2,3]
    nat = _recursiveType natData

goldenVsPretty :: PrettyPlc a => String -> ExceptT BSL.ByteString IO a -> TestTree
goldenVsPretty name value = goldenVsString name ("test/Evaluation/Golden/" ++ name ++ ".plc.golden") $ either id (BSL.fromStrict . encodeUtf8 . docText . prettyPlcClassicDebug) <$> runExceptT value

test_evaluateCk :: TestTree
test_evaluateCk = testGroup "evaluateCk"
    [ testGroup "props" $ fromInterestingTermGens (\name -> testProperty name . propEvaluate evaluateCk)
    , goldenVsPretty "even2" . pure . evaluateCk $ Apply () even $ metaIntegerToNat 2
    , goldenVsPretty "even3" . pure . evaluateCk $ Apply () even $ metaIntegerToNat 3
    , goldenVsPretty "evenList" . pure . evaluateCk $
          Apply () (natSum 64) $ Apply () evenList smallNatList
    ]
