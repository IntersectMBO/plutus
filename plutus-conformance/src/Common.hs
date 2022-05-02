{-# LANGUAGE OverloadedStrings #-}

module PlutusConformance.Common where

import Data.Text hiding (map)
import Data.Text.IO
import PlutusCore as PLC
import PlutusCore.Pretty
import Prelude hiding (readFile)
import Test.Tasty
import Test.Tasty.Golden
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
    if length lFilepaths == length lRes == length lProgs then
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
mkTestCases (hdTests:tlTests) runner =
    testCase (testName hdTests) ((expected hdTests) @=? (runner (inputProg hdTests))) : mkTestCases tlTests runner
mkTestCases [] runner = []

testUplcEvaluation :: [TestContent] -> (UplcProg -> IO (EvaluationResult UplcProg)) -> TestTree
testUplcEvaluation lTest runner =
    testGroup "UPLC evaluation tests" $ mkTestCases lTest runner

testUplcEvaluationTextual :: (Text -> IO Text) -> TestTree
testUplcEvaluationTextual runner = testUplcEvaluation (evalUplcProg . UPLC.parseProgram <$> runner . pack . show)

-- runAgdaImpl = callProcess “agdaImpl …”

-- testUplcEvaluation runAgdaImpl
