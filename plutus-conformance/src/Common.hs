{-# LANGUAGE OverloadedStrings #-}

module Common where

import GHC.IO (unsafePerformIO)
import PlutusCore as PLC
import Prelude hiding (readFile)
import Test.Tasty
import Test.Tasty.HUnit
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (unsafeEvaluateCekNoEmit)

data TestContent =
    MkTestContent {
        testName    :: FilePath
        , expected  :: EvaluationResult UplcProg
        , inputProg :: UplcProg
    }

mkTestContents :: [FilePath] -> [EvaluationResult UplcProg] -> [UplcProg] -> [TestContent]
mkTestContents lFilepaths lRes lProgs =
    if length lFilepaths == length lRes && length  lRes == length lProgs then
        [MkTestContent file res prog | file <- lFilepaths, res <- lRes, prog <- lProgs]
    else
        error $ "Cannot run the tests because the number of input and output programs are not the same. " <>
            "Number of input files: " <> show (length lProgs) <>
            " Number of output files: " <> show (length lRes) <>
            " Make sure all your input programs have an accompanying .expected file."

type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

termToProg :: UPLC.Term Name DefaultUni DefaultFun () -> UplcProg
termToProg = UPLC.Program () (PLC.defaultVersion ())

evalUplcProg :: UplcProg -> IO (EvaluationResult UplcProg)
evalUplcProg p = pure $
    fmap
        termToProg
        (unsafeEvaluateCekNoEmit PLC.defaultCekParameters (UPLC._progTerm p))

stripePosProg :: UPLC.Program Name DefaultUni DefaultFun SourcePos -> UplcProg
stripePosProg (UPLC.Program _ann (Version _ num1 num2 num3) tm) = UPLC.Program () (Version () num1 num2 num3) (stripePosTm tm)

stripePosTm :: UPLC.Term Name DefaultUni DefaultFun SourcePos -> UPLC.Term Name DefaultUni DefaultFun ()
stripePosTm (UPLC.Var _ name)       = UPLC.Var () name
stripePosTm (UPLC.LamAbs _ name tm) = UPLC.LamAbs () name (stripePosTm tm)
stripePosTm (UPLC.Apply _ tm1 tm2)  = UPLC.Apply () (stripePosTm tm1) (stripePosTm tm2)
stripePosTm (UPLC.Force _ tm)       = UPLC.Force () (stripePosTm tm)
stripePosTm (UPLC.Delay _ tm)       = UPLC.Delay () (stripePosTm tm)
stripePosTm (UPLC.Constant _ val)   = UPLC.Constant () val
stripePosTm (UPLC.Builtin _ f)      = UPLC.Builtin () f
stripePosTm (UPLC.Error _)          = UPLC.Error ()

mkTestCases :: [TestContent] -> (UplcProg -> IO (EvaluationResult UplcProg)) -> [TestTree]
mkTestCases tests runner
  = [ unsafePerformIO $ do
      result <- runner (inputProg test)
      pure $ testCase (testName test) (expected test @=? result)
       | test <- tests]

testUplcEvaluation :: [TestContent] -> (UplcProg -> IO (EvaluationResult UplcProg)) -> TestTree
testUplcEvaluation lTest runner =
    testGroup "UPLC evaluation tests" $ mkTestCases lTest runner
