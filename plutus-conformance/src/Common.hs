{-# LANGUAGE OverloadedStrings #-}

module Common where

import Control.Monad.Error.Class
import Data.Text qualified as T
import GHC.IO (unsafePerformIO)
import PlutusCore as PLC
import PlutusCore.Error (AsParserErrorBundle)
import Prelude hiding (readFile)
import Test.Tasty
import Test.Tasty.HUnit
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (unsafeEvaluateCekNoEmit)
import UntypedPlutusCore.Parser as UPLC

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

mkTestCases :: [TestContent] -> (UplcProg -> IO (EvaluationResult UplcProg)) -> [TestTree]
mkTestCases tests runner
  = [ unsafePerformIO $ do
      result <- runner (inputProg test)
      pure $ testCase (testName test) (expected test @=? result)
       | test <- tests]

testUplcEvaluation :: [TestContent] -> (UplcProg -> IO (EvaluationResult UplcProg)) -> TestTree
testUplcEvaluation lTest runner =
    testGroup "UPLC evaluation tests" $ mkTestCases lTest runner
