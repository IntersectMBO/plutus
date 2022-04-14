{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

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

main :: IO ()
main = do
    inputFiles <- findByExtension [".uplc"] "plutus-conformance/uplc/evaluation/textual-inputs"
    outputFiles <- findByExtension [".expected"] "plutus-conformance/uplc/evaluation/outputs"
    lProg <- traverse (readFile) inputFiles
    lEvaluatedRes <- traverse readFile outputFiles
    let tests = mkTestContents inputFiles lEvaluatedRes lProg
    defaultMain undefined --(testUplcEvaluationTextual lProg)

data TestContent =
    MkTestContent {
        testName    :: FilePath
        , expected  :: EvaluationResult UplcProg
        , inputProg :: UplcProg
    }

mkTestContents :: [FilePath] -> [EvaluationResult UplcProg] -> [UplcProg] -> [TestContent]
mkTestContents (hdF:tlF) (hdR:tlR) (hdI:tlI) =
    MkTestContent hdF hdR hdI : mkTestContents tlF tlR tlI
mkTestContents [] [] [] = []

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
testUplcEvaluationTextual runner = testUplcEvaluation undefined undefined --(evalUplcProg . UPLC.parseProgram <$> runner . pack . show)

-- runAgdaImpl = callProcess “agdaImpl …”

-- testUplcEvaluation runAgdaImpl
