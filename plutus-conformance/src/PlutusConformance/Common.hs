{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Plutus conformance test suite library.
module PlutusConformance.Common where

import Data.Maybe (fromJust)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import PlutusCore.Annotation
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModelParamsForTesting)
import PlutusCore.Name.Unique (Name)
import PlutusCore.Quote (runQuoteT)
import PlutusPrelude (Pretty (pretty), display, void)
import System.Directory
import System.FilePath (takeBaseName, takeFileName, (<.>), (</>))
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.Extras (goldenVsDocM)
import Test.Tasty.Golden (findByExtension)
import Test.Tasty.Golden.Advanced (goldenTest)
import Test.Tasty.Providers (TestTree)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Parser qualified as UPLC
import Witherable (Witherable (wither))

-- Common functions for all tests

{-| The default shown text when a parse error occurs.
We don't want to show the detailed parse errors so that
users of the test suite can produce the expected output more easily. -}
shownParseError :: T.Text
shownParseError = "parse error"

-- | The default shown text when evaluation fails.
shownEvaluationFailure :: T.Text
shownEvaluationFailure = "evaluation failure"

-- | The default parser to parse UPLC program inputs.
parseTxt
  :: T.Text
  -> Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SrcSpan)
parseTxt resTxt = runQuoteT $ UPLC.parseProgram resTxt

-- | The input/output UPLC program type.
type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

-- UPLC evaluation test functions

-- convenience type synonym
type UplcEvaluatorFun res = UplcProg -> Maybe res

-- TODO: consider splitting up the evaluator with costing into a part that
-- parses the model and a part that consumes it. Currently the tests are fast
-- enough regardless so it doesn't matter.

-- | The evaluator to be tested.
data UplcEvaluator
  = -- | An evaluator that just produces an output program, or fails.
    UplcEvaluatorWithoutCosting (UplcEvaluatorFun UplcProg)
  | {-| An evaluator that produces an output program along with the cost of
    evaluating it, or fails. Note that nothing cares about the cost of failing
    programs, so we don't test for conformance there. -}
    UplcEvaluatorWithCosting
      (CostModelParams -> UplcEvaluatorFun (UplcProg, ExBudget))

{-| Walk a file tree, making test groups for directories with subdirectories,
   and test cases for directories without.  We expect every test directory to
   contain a single `.uplc` file whose name matches that of the directory. For
   example, the directory `modInteger-15` should contain `modInteger-15.uplc`,
   and that file should contain a textual UPLC program.  The directory should
   also contain golden files `modInteger-15.uplc.expected`, containing the
   expected output of the program, and `modInteger-15.uplc.budget.expected`,
   containing the expected execution budget, although these will be created by
   the testing machinery if they aren't already present. -}
discoverTests
  :: UplcEvaluator
  -- ^ The evaluator to be tested.
  -> CostModelParams
  -> (FilePath -> Bool)
  {-^ A function that takes a test directory and returns a Bool indicating
  whether the evaluation test for the file in that directory is expected to
  fail. -}
  -> (FilePath -> Bool)
  {-^ A function that takes a test directory and returns a Bool indicating
  whether the budget test for the file in that directory is expected to fail. -}
  -> FilePath
  -- ^ The directory to search for tests.
  -> IO TestTree
discoverTests eval modelParams evaluationFailureExpected budgetFailureExpected =
  go
  where
    go dir = do
      let name = takeBaseName dir
      children <- listDirectory dir
      subdirs <- flip wither children $ \child -> do
        let fullPath = dir </> child
        isDir <- doesDirectoryExist fullPath
        pure $ if isDir then Just fullPath else Nothing
      if null subdirs
        -- no children, this is a test case directory
        then do
          -- Check that the  directory <dir> contains exactly one .uplc file
          -- and that it's called <name>.uplc, where <name> is the final path
          -- component of <dir>.
          uplcFiles <- findByExtension [".uplc"] dir
          let expectedInputFile = takeFileName dir <.> ".uplc"
              inputFilePath =
                case uplcFiles of
                  [] ->
                    error $
                      "Input file "
                        ++ expectedInputFile
                        ++ " missing in " <> dir
                  _ : _ : _ -> error $ "More than one .uplc file in " <> dir
                  [file] ->
                    if takeFileName file /= expectedInputFile
                      then
                        error $
                          "Found file "
                            ++ takeFileName file
                            ++ " in directory "
                            ++ dir
                            ++ " (expected "
                            ++ expectedInputFile
                            ++ ")"
                      else file
          let tests = case eval of
                UplcEvaluatorWithCosting f ->
                  testGroup
                    name
                    [ testForEval dir inputFilePath (fmap fst . f modelParams)
                    , testForBudget dir inputFilePath (fmap snd . f modelParams)
                    ]
                UplcEvaluatorWithoutCosting f -> testForEval dir inputFilePath f
          pure tests
        -- has children, so it's a grouping directory
        else testGroup name <$> traverse go subdirs
    testForEval :: FilePath -> String -> UplcEvaluatorFun UplcProg -> TestTree
    testForEval dir inputFilePath e =
      let goldenFilePath = inputFilePath <.> "expected"
          test =
            goldenTest
              (takeFileName inputFilePath ++ " (evaluation)")
              -- get the golden test value
              (expectedToProg <$> T.readFile goldenFilePath)
              -- get the tested value
              (getTestedValue e inputFilePath)
              (\x y -> pure $ compareAlphaEq x y) -- comparison function
              (updateGoldenFile goldenFilePath) -- update the golden file
       in possiblyFailingTest (evaluationFailureExpected dir) test
    testForBudget :: FilePath -> String -> UplcEvaluatorFun ExBudget -> TestTree
    testForBudget dir inputFilePath e =
      let goldenFilePath = inputFilePath <.> "budget" <.> "expected"
          prettyEither (Left l) = pretty l
          prettyEither (Right r) = pretty r
          test =
            goldenVsDocM
              (takeFileName inputFilePath ++ " (budget)")
              goldenFilePath
              (prettyEither <$> getTestedValue e inputFilePath)
       in possiblyFailingTest (budgetFailureExpected dir) test
    possiblyFailingTest :: Bool -> TestTree -> TestTree
    possiblyFailingTest failureExpected test =
      if failureExpected
        then ignoreTest test
        -- TODO: ^ this should really be `expectFail`, but that behaves strangely
        -- with `--accept` (the golden files for the failing tests get updated:
        -- see https://github.com/IntersectMBO/plutus/issues/6714 and
        -- https://github.com/nomeata/tasty-expected-failure/issues/27.
        -- If/when that gets fixed `ignoreTest` should be changed to `expectFail`.
        else test

{-| Turn the expected file content in text to a `UplcProg` unless the expected
result is a parse or evaluation error. -}
expectedToProg :: T.Text -> Either T.Text UplcProg
expectedToProg txt
  | txt == shownEvaluationFailure =
      Left txt
  | txt == shownParseError =
      Left txt
  | otherwise =
      case parseTxt txt of
        Left _ -> Left txt
        Right p -> Right $ void p

{-| Get the tested value from a file (in this case a textual UPLC source
file). The tested value is either the shown parse error or evaluation error,
or a `UplcProg`. -}
getTestedValue
  :: UplcEvaluatorFun res
  -> FilePath
  -> IO (Either T.Text res)
getTestedValue eval file = do
  input <- T.readFile file
  pure $ case parseTxt input of
    Left _ -> Left shownParseError
    Right p ->
      case eval (void p) of
        Nothing -> Left shownEvaluationFailure
        Just prog -> Right prog

{-| The comparison function used for the golden test.
This function checks alpha-equivalence of programs when the output is a program. -}
compareAlphaEq
  :: Either T.Text UplcProg
  -- ^ golden value
  -> Either T.Text UplcProg
  -- ^ tested value
  -> Maybe String
  {-^ If two values are the same, it returns `Nothing`.
  If they are different, it returns an error that will be printed to the user. -}
compareAlphaEq (Left expectedTxt) (Left actualTxt) =
  if actualTxt == expectedTxt
    then Nothing
    else
      Just $
        "Test failed, the output failed to parse or evaluate: \n"
          <> T.unpack actualTxt
compareAlphaEq (Right expected) (Right actual) =
  if actual == expected
    then Nothing
    else
      Just $
        "Test failed, the output was successfully parsed and evaluated, \
        \but it isn't as expected. "
          <> "The output program is: \n"
          <> display actual
          <> "\n The output program, with the unique names shown is: \n"
          -- using `show` here so that the unique names will show
          <> show actual
          -- the user can look at the .expected file,
          -- but they can't see the unique names
          <> "\n But the expected result, with the unique names shown is: \n"
          <> show expected
compareAlphaEq (Right expected) (Left actualTxt) =
  pure $
    "Test failed, the output failed to parse or evaluate: \n"
      <> T.unpack actualTxt
      <> "\n But the expected result, with the unique names shown is: \n"
      <> show expected
compareAlphaEq (Left txt) (Right actual) =
  {- this is to catch the case when the expected program failed to parse because
  our parser doesn't support `data` atm. In this case, if the textual program is
  the same as the actual, the test succeeds. -}
  if txt == display actual
    then Nothing
    else
      Just $
        "Test failed, the output was successfully parsed and evaluated, \
        \but it isn't as expected. "
          <> "The output program is: "
          <> display actual
          <> ". But the expected result is: "
          <> T.unpack txt

{-| Update the golden file with the tested value.
TODO abstract out for other tests. -}
updateGoldenFile
  :: FilePath
  -- ^ the path to write the golden file to
  -> Either T.Text UplcProg
  -> IO ()
updateGoldenFile goldenPath (Left txt) = T.writeFile goldenPath txt
updateGoldenFile goldenPath (Right p) = T.writeFile goldenPath (display p)

{-| Run the UPLC evaluation tests given an `evaluator` that evaluates UPLC
programs. -}
runUplcEvalTests
  :: UplcEvaluator
  -- ^ The action to run the input through for the tests.
  -> (FilePath -> Bool)
  {-^ A function that takes a test name and returns
  whether it should labelled as `ExpectedFailure`. -}
  -> (FilePath -> Bool)
  {-^ A function that takes a test name and returns
  whether it should labelled as `ExpectedBudgetFailure`. -}
  -> IO ()
runUplcEvalTests eval expectedFailTests expectedBudgetFailTests = do
  let params = fromJust defaultCostModelParamsForTesting
  tests <-
    discoverTests
      eval
      params
      expectedFailTests
      expectedBudgetFailTests
      "test-cases/uplc/evaluation"
  defaultMain $ testGroup "UPLC evaluation tests" [tests]
