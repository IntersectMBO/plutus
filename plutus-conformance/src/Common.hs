{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp  #-}
module Common where

import Data.Text (Text, unpack)
import PlutusCore.Core (defaultVersion)
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParserErrorBundle (ParseErrorB))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import PlutusCore.Evaluation.Result (EvaluationResult (..))
import PlutusCore.Name (Name)
import PlutusCore.Quote (runQuoteT)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@=?))
import Text.Megaparsec (SourcePos, errorBundlePretty)
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (unsafeEvaluateCekNoEmit)
import UntypedPlutusCore.Parser (parseProgram)

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
       , expected  :: EvaluationResult UplcProg
       , inputProg :: UplcProg
   }

mkTestContents :: [FilePath] -> [EvaluationResult UplcProg] -> [UplcProg] -> [TestContent]
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

mkTestCases :: [TestContent] -> (UplcProg -> EvaluationResult UplcProg) -> IO [TestTree]
mkTestCases tests runner =
    do
        let results = fmap (runner . inputProg) tests
        pure $
            [testCase (testName test) (expected test @=? result) | test <- tests | result <- results]


testUplcEvaluation :: [TestContent] -> (UplcProg -> EvaluationResult UplcProg) -> IO TestTree
testUplcEvaluation lTest runner = do
    testContents <- mkTestCases lTest runner
    pure $ testGroup "UPLC evaluation tests" testContents

shownEvaluationFailure :: Text
shownEvaluationFailure = "evaluation failure"

textToEvalRes :: Text -> EvaluationResult UplcProg
textToEvalRes txt =
    if txt == shownEvaluationFailure then
        EvaluationFailure
    else do
        let parsed = runQuoteT $ parseProgram txt :: Either ParserErrorBundle (UPLC.Program
                      Name DefaultUni DefaultFun SourcePos)
        case parsed of
            Left (ParseErrorB err) -> error $
                unlines
                    ["textToEvalRes: this should not happen. Parsing of result"
                    , unpack txt
                    , "failed with error:"
                    , errorBundlePretty err
                    ]
            Right prog -> EvaluationSuccess $ () <$ prog

parseText :: Text -> UplcProg
parseText txt =
    let parsed = runQuoteT $ parseProgram txt :: Either ParserErrorBundle (UPLC.Program
                      Name DefaultUni DefaultFun SourcePos)
    in
    case parsed of
        Left (ParseErrorB err) -> error $
            unlines
                ["parseText: this should not happen. Parsing of program"
                , unpack txt
                , "failed with error:"
                , errorBundlePretty err
                ]
        Right prog -> () <$ prog
