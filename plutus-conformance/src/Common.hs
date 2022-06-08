{-# LANGUAGE OverloadedStrings #-}

module Common where

import Control.Exception (SomeException, evaluate, try)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import PlutusCore.Core (defaultVersion)
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParserErrorBundle (ParseErrorB))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import PlutusCore.Evaluation.Result (EvaluationResult (..))
import PlutusCore.Name (Name)
import PlutusCore.Quote (runQuoteT)
import PlutusPrelude (Pretty (pretty), Render (render), zipWith3Exact, zipWithExact)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (findByExtension)
import Test.Tasty.HUnit (testCase, (@=?))
import Text.Megaparsec (SourcePos)
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (unsafeEvaluateCekNoEmit)
import UntypedPlutusCore.Parser qualified as UPLC

data TestContent =
   MkTestContent {
       testName    :: FilePath
       , expected  :: T.Text
       , inputProg :: T.Text
   }

mkTestContents ::
    [FilePath] ->
        [T.Text] ->
            [T.Text] -> [TestContent]
mkTestContents lFilepaths lRes lProgs =
    case zipWith3Exact (\f r p -> MkTestContent f r p) lFilepaths lRes lProgs of
        Just tests -> tests
        Nothing -> error $ unlines
            ["mkTestContents: Cannot run the tests because the number of input and output programs are not the same. "
            , "Number of input files: "
            , show (length lProgs)
            , " Number of output files: "
            , show (length lRes)
            , " Make sure all your input programs have an accompanying .expected file."
            ]

shownParseError :: T.Text
shownParseError = "parse error"

shownEvaluationFailure :: T.Text
shownEvaluationFailure = "evaluation failure"

-- For UPLC evaluation tests

type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

termToProg :: UPLC.Term Name DefaultUni DefaultFun () -> UplcProg
termToProg = UPLC.Program () (defaultVersion ())

{- using the unsafe version of evaluate here so that it has a more generic signature.
Any exceptions will be caught for any input runner in the tests, including our `evalUplcProg`.
 -}
evalUplcProg :: UplcProg -> EvaluationResult UplcProg
evalUplcProg p =
    fmap
        termToProg
        (unsafeEvaluateCekNoEmit defaultCekParameters (UPLC._progTerm p))

mkResult :: (UplcProg -> EvaluationResult UplcProg) ->
    Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SourcePos) ->
        IO T.Text
mkResult _ (Left (ParseErrorB _err)) = pure shownParseError
mkResult runner (Right prog)        = do
    maybeException <- try (evaluate $ runner (() <$ prog)):: IO (Either SomeException (EvaluationResult UplcProg))
    case maybeException of
        Left _                  -> pure shownEvaluationFailure
        -- it doesn't matter how the evaluation fail, they're all "evaluation failure"
        Right EvaluationFailure -> pure shownEvaluationFailure
        Right a                 -> pure $ render $ pretty a

parseTxt :: T.Text -> Either ParserErrorBundle (UPLC.Program
              Name DefaultUni DefaultFun SourcePos)
parseTxt resTxt = runQuoteT $ UPLC.parseProgram resTxt

mkTestCases :: [TestContent] -> (UplcProg -> EvaluationResult UplcProg) -> IO [TestTree]
mkTestCases tests runner =
    do
        results <- traverse (mkResult runner . parseTxt . inputProg) tests
        -- make everything (name, assertion) all at once to make sure pairings are correct
        let maybeNameAssertion =
                zipWithExact (\t res -> (testName t, expected t @=? res)) tests results
        case maybeNameAssertion of
            Just lNameAssertion -> pure $
                fmap (\a -> uncurry testCase a) lNameAssertion
            Nothing -> error "mkTestCases: Number of tests and results don't match."


testUplcEvaluation :: [TestContent] -> (UplcProg -> EvaluationResult UplcProg) -> IO TestTree
testUplcEvaluation lTest runner = do
    testContents <- mkTestCases lTest runner
    pure $ testGroup "UPLC evaluation tests" testContents

runTests :: (UplcProg -> EvaluationResult UplcProg) -> IO ()
runTests runner = do
    inputFiles <- findByExtension [".uplc"] "uplc/evaluation/"
    outputFiles <- findByExtension [".expected"] "uplc/evaluation/"
    lProgTxt <- traverse T.readFile inputFiles
    lEvaluatedRes <- traverse T.readFile outputFiles
    if length inputFiles == length lProgTxt && length lEvaluatedRes == length lProgTxt then
        do
        let testContents = mkTestContents inputFiles lEvaluatedRes lProgTxt
        testTree <- testUplcEvaluation testContents runner
        defaultMain testTree
    else
        error $ unlines
            ["Cannot run the tests because the number of input and output programs are not the same. "
            , "Number of input files: "
            , show (length lProgTxt)
            , " Number of output files: "
            , show (length lEvaluatedRes)
            , " Make sure all your input programs have an accompanying .expected file."
            ]
