{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp  #-}
module Common where

import Data.Text qualified as T
import PlutusCore.Core (defaultVersion)
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParserErrorBundle (ParseErrorB))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import PlutusCore.Evaluation.Result (EvaluationResult (..))
import PlutusCore.Name (Name)
import PlutusCore.Quote (runQuoteT)
import System.FilePath (takeBaseName)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@=?))
import Text.Megaparsec (SourcePos, errorBundlePretty)
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (unsafeEvaluateCekNoEmit)
import UntypedPlutusCore.Parser qualified as UPLC

type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

termToProg :: UPLC.Term Name DefaultUni DefaultFun () -> UplcProg
termToProg = UPLC.Program () (defaultVersion ())

evalUplcProg :: UplcProg -> EvaluationResult UplcProg
evalUplcProg p =
    fmap
        termToProg
        (unsafeEvaluateCekNoEmit defaultCekParameters (UPLC._progTerm p))

data TestContent =
   MkTestContent {
       testName    :: FilePath
       , expected  :: Either T.Text (EvaluationResult UplcProg)
       , inputProg :: T.Text
   }

mkTestContents ::
    [FilePath] ->
        [Either T.Text (EvaluationResult UplcProg)] ->
            [T.Text] -> [TestContent]
mkTestContents lFilepaths lRes lProgs =
    if length lFilepaths == length lRes && length  lRes == length lProgs then
        zipWith3 (\f r p -> MkTestContent f r p) lFilepaths lRes lProgs
    else
        error $ unlines
            ["mkTestContents: Cannot run the tests because the number of input and output programs are not the same. "
            , "Number of input files: "
            , show (length lProgs)
            , " Number of output files: "
            , show (length lRes)
            , " Make sure all your input programs have an accompanying .expected file."
            ]

parseProg :: TestContent -> Either ParserErrorBundle (UPLC.Program
                      Name DefaultUni DefaultFun SourcePos)
parseProg test = runQuoteT $ UPLC.parse UPLC.program (takeBaseName (testName test)) $ inputProg test

mkResult :: (UplcProg -> EvaluationResult UplcProg) ->
    Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SourcePos) ->
        Either T.Text (EvaluationResult UplcProg)
mkResult _ (Left (ParseErrorB err)) = Left $ T.pack $ errorBundlePretty err
mkResult runner (Right prog)        = Right $ runner $ () <$ prog

mkTestCases :: [TestContent] -> (UplcProg -> EvaluationResult UplcProg) -> IO [TestTree]
mkTestCases tests runner =
    do
        let
            results = fmap (mkResult runner . parseProg) tests
        pure $
            [testCase (testName test) (expected test @=? result) | test <- tests | result <- results]


testUplcEvaluation :: [TestContent] -> (UplcProg -> EvaluationResult UplcProg) -> IO TestTree
testUplcEvaluation lTest runner = do
    testContents <- mkTestCases lTest runner
    pure $ testGroup "UPLC evaluation tests" testContents

shownEvaluationFailure :: T.Text
shownEvaluationFailure = "evaluation failure"

textToEvalRes :: T.Text -> Either T.Text (EvaluationResult UplcProg)
textToEvalRes txt =
    if txt == shownEvaluationFailure then
        Right EvaluationFailure
    else
        let parseTxt :: T.Text -> Either ParserErrorBundle (UPLC.Program
                      Name DefaultUni DefaultFun SourcePos)
            parseTxt resTxt = runQuoteT $ UPLC.parseProgram resTxt
        in
            case parseTxt txt of
                Left _     -> Left txt
                Right prog -> Right $ EvaluationSuccess $ () <$ prog
