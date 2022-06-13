{-# LANGUAGE OverloadedStrings #-}

{- | Plutus conformance test suite library. -}
module PlutusConformance.Common where

import Control.DeepSeq (force)
import Control.Exception (SomeException, evaluate, try)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import PlutusCore.Core (defaultVersion)
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParserErrorBundle (ParseErrorB))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import PlutusCore.Name (Name)
import PlutusCore.Quote (runQuoteT)
import PlutusPrelude
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (findByExtension)
import Test.Tasty.HUnit (testCase, (@=?))
import Text.Megaparsec (SourcePos)
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (evaluateCekNoEmit)
import UntypedPlutusCore.Parser qualified as UPLC

-- | A TestContent contains what you need to run a test.
data TestContent =
   MkTestContent {
       -- | The path of the input file. This is also used to name the test.
       testName    :: FilePath
       -- | The expected output of the test in `Text`.
       , expected  :: T.Text
       -- | The input to be tested, in `Text`.
       , inputProg :: T.Text
   }

{- | Create a list of `TestContent` with the given lists.
The lengths of the input lists have to be the same, otherwise, an error occurs. -}
mkTestContents ::
    [FilePath] -- ^ The list of paths of the input files.
    -> [T.Text] -- ^ The list of expected outputs.
    -> [T.Text] -- ^ The list of the inputs.
    -> [TestContent]
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

{- | The default shown text when a parse error occurs.
We don't want to show the detailed parse errors so that
users of the test suite can produce this expected outputs more easily. -}
shownParseError :: T.Text
shownParseError = "parse error"

-- | The default shown text when evaluation fails.
shownEvaluationFailure :: T.Text
shownEvaluationFailure = "evaluation failure"

-- For UPLC evaluation tests

type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

termToProg :: UPLC.Term Name DefaultUni DefaultFun () -> UplcProg
termToProg = UPLC.Program () (defaultVersion ())

-- | Our `runner` for the UPLC tests is the CEK machine.
evalUplcProg :: UplcProg -> Maybe UplcProg
evalUplcProg p =
    let eitherExceptionProg =
            fmap
                termToProg
                (evaluateCekNoEmit defaultCekParameters (UPLC._progTerm p))
    in
        case eitherExceptionProg of
            Left _     -> Nothing
            Right prog -> Just prog

{- | Run the inputs with the runner and return the results, in `Text`.
When fail, the results are the default texts for parse error or evaluation failure. -}
mkResult ::
    (UplcProg -> Maybe UplcProg) -- ^ The `runner` to run the test inputs with.
    -> Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SourcePos)
    -- ^ The result of parsing.
    -> IO T.Text -- ^ The result in `Text`.
mkResult _ (Left (ParseErrorB _err)) = pure shownParseError
mkResult runner (Right prog)        = do
    maybeException <- try (evaluate $ force $ runner (() <$ prog)):: IO (Either SomeException (Maybe UplcProg))
    case maybeException of
        Left _         -> pure shownEvaluationFailure
        -- it doesn't matter how the evaluation fail, they're all "evaluation failure"
        Right Nothing  -> pure shownEvaluationFailure
        Right (Just a) -> pure $ display a

-- | The default parser to parse the inputs.
parseTxt ::
    T.Text
    -> Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SourcePos)
parseTxt resTxt = runQuoteT $ UPLC.parseProgram resTxt

-- | Build the test tree given a list of `TestContent` and the runner.
-- TODO maybe abstract this for other tests too if it takes in `mkResult` and `runner`.
mkTestCases :: [TestContent] -> (UplcProg -> Maybe UplcProg) -> IO TestTree
mkTestCases lTest runner = do
    results <- for lTest (mkResult runner . parseTxt . inputProg)
    -- make everything (name, assertion) all at once to make sure pairings are correct
    let maybeNameAssertion =
            zipWithExact (\t res -> (testName t, expected t @=? res)) lTest results
    testContents <- case maybeNameAssertion of
        Just lNameAssertion -> pure $
            fmap (\a -> uncurry testCase a) lNameAssertion
        Nothing -> error "mkTestCases: Number of tests and results don't match."
    pure $ testGroup "UPLC evaluation tests" testContents

-- | Run the tests given a `runner`.
runTests ::
    (UplcProg -> Maybe UplcProg)-- ^ The action to run the input through for the tests.
    -> IO ()
runTests runner = do
    inputFiles <- findByExtension [".uplc"] "uplc/evaluation/"
    outputFiles <- findByExtension [".expected"] "uplc/evaluation/"
    lProgTxt <- for inputFiles T.readFile
    lEvaluatedRes <- for outputFiles T.readFile
    let testContents = mkTestContents inputFiles lEvaluatedRes lProgTxt
    testTree <- mkTestCases testContents runner
    defaultMain testTree
