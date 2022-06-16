{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}

{- | Plutus conformance test suite library. -}
module PlutusConformance.Common where

import Control.DeepSeq (force)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import PlutusCore.Core (defaultVersion)
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParserErrorBundle (ParseErrorB))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import PlutusCore.Name (Name)
import PlutusCore.Quote (runQuoteT)
import PlutusPrelude
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.Golden (findByExtension)
import Test.Tasty.HUnit (testCase, (@=?))
import Test.Tasty.Providers
import Text.Megaparsec (SourcePos)
import UnliftIO.Exception
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (evaluateCekNoEmit)
import UntypedPlutusCore.Parser qualified as UPLC

-- Common functions for all tests

-- | A TestContent contains the input file path, input and output file contents.
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

{- | Run an input with the `runner` and return the result, in `Text`.
When fail, the result is either the default text for parse error or evaluation failure. -}
mkResult ::
    (UplcProg -> Maybe UplcProg) -- ^ The `runner` to run the test inputs with.
    -> Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SourcePos)
    -- ^ The result of parsing.
    -> IO T.Text -- ^ The result of the `runner` in `Text`.
mkResult _ (Left (ParseErrorB _err)) = pure shownParseError
mkResult runner (Right prog)        = do
    -- catch exceptions from `runner` and keep going unless it's an async exception.
    maybeException <- trySyncOrAsync (evaluate $ force $ runner (() <$ prog)):: IO (Either SomeException (Maybe UplcProg))
    case maybeException of
        Left e       ->
            if isAsyncException e then
                throwIO e
            else
                pure shownEvaluationFailure
        -- it doesn't matter how the evaluation fail, they're all "evaluation failure"
        Right Nothing  -> pure shownEvaluationFailure
        Right (Just a) -> pure $ display a

-- | The default parser to parse the inputs.
parseTxt ::
    T.Text
    -> Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SourcePos)
parseTxt resTxt = runQuoteT $ UPLC.parseProgram resTxt

-- | Build a test given the runner and a `TestContent`.
-- TODO maybe abstract this for other tests too if it takes in `mkResult`.
mkUplcTestCase :: (UplcProg -> Maybe UplcProg) -> TestContent -> TestTree
mkUplcTestCase runner test =
    testCase (testName test) (
        do r <- mkResult runner (parseTxt (inputProg test))
           expected test @=? r)

-- | Run the tests given a `runner` that evaluates UPLC programs.
runUplcEvalTests ::
    (UplcProg -> Maybe UplcProg)-- ^ The action to run the input through for the tests.
    -> IO ()
runUplcEvalTests runner = do
    inputFiles <- findByExtension [".uplc"] "uplc/evaluation/"
    outputFiles <- findByExtension [".expected"] "uplc/evaluation/"
    lProgTxt <- for inputFiles T.readFile
    lEvaluatedRes <- for outputFiles T.readFile
    let testContents = mkTestContents inputFiles lEvaluatedRes lProgTxt
    defaultMain $ testGroup "UPLC evaluation tests" $ fmap (mkUplcTestCase runner) testContents
