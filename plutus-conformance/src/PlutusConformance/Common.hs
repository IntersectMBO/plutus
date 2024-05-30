{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}

{- | Plutus conformance test suite library. -}
module PlutusConformance.Common where

import PlutusCore.Annotation
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModelParamsForTesting)
import PlutusCore.Name.Unique (Name)
import PlutusCore.Quote (runQuoteT)
import PlutusPrelude (Pretty (pretty), display, void)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Parser qualified as UPLC


import Data.Maybe (fromJust)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import System.Directory
import System.FilePath (takeBaseName, (<.>), (</>))
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.Extras (goldenVsDocM)
import Test.Tasty.Golden (findByExtension)
import Test.Tasty.Golden.Advanced (goldenTest)
import Test.Tasty.Providers (TestTree)
import Witherable (Witherable (wither))

-- Common functions for all tests

{- | The default shown text when a parse error occurs.
We don't want to show the detailed parse errors so that
users of the test suite can produce the expected output more easily. -}
shownParseError :: T.Text
shownParseError = "parse error"

-- | The default shown text when evaluation fails.
shownEvaluationFailure :: T.Text
shownEvaluationFailure = "evaluation failure"

-- | The default parser to parse UPLC program inputs.
parseTxt ::
    T.Text
    -> Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SrcSpan)
parseTxt resTxt = runQuoteT $ UPLC.parseProgram resTxt

-- | The input/output UPLC program type.
type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

-- UPLC evaluation test functions

-- convenience type synonym
type UplcEvaluatorFun res = UplcProg -> Maybe res

-- TODO: consider splitting up the evaluator with costing into a part that parses the model
-- and a part that consumes it. Currently the tests are fast enough regardless so it doesn't
-- matter.
-- | The evaluator to be tested.
data UplcEvaluator =
  -- | An evaluator that just produces an output program, or fails.
  UplcEvaluatorWithoutCosting (UplcEvaluatorFun UplcProg)
  -- | An evaluator that produces an output program along with the cost of evaluating it, or fails.
  -- Note that nothing cares about the cost of failing programs, so we don't test for conformance
  -- there.
  | UplcEvaluatorWithCosting (CostModelParams -> UplcEvaluatorFun (UplcProg, ExBudget))

-- | Walk a file tree, making test groups for directories with subdirectories,
-- and test cases for directories without.
discoverTests
  :: UplcEvaluator -- ^ The evaluator to be tested.
  -> CostModelParams
  -> (FilePath -> Bool)
  -- ^ A function that takes a test name and returns
  -- whether it should be labelled as `ExpectedFailure`.
  -> FilePath -- ^ The directory to search for tests.
  -> IO TestTree
discoverTests eval modelParams expectedFailureFn = go
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
        then
            let tests = case eval of
                    UplcEvaluatorWithCosting f -> testGroup name
                        [ testForEval dir name (fmap fst . f modelParams)
                        , testForBudget dir name (fmap snd . f modelParams)
                        ]
                    UplcEvaluatorWithoutCosting f -> testForEval dir name f
            in
                -- if the test is expected to fail, mark it so.
                if expectedFailureFn dir
                then pure $ expectFail tests
                -- the test isn't expected to fail, make the `TestTree` as usual.
                else pure tests
        -- has children, so it's a grouping directory
        else testGroup name <$> traverse go subdirs
    testForEval :: FilePath -> String -> UplcEvaluatorFun UplcProg -> TestTree
    testForEval dir name e =
        let goldenFilePath = dir </> name <.> "uplc.expected"
        in goldenTest
            (name ++ " (evaluation)")
            -- get the golden test value
            (expectedToProg <$> T.readFile goldenFilePath)
            -- get the tested value
            (getTestedValue e dir)
            (\ x y -> pure $ compareAlphaEq x y) -- comparison function
            (updateGoldenFile goldenFilePath) -- update the golden file

    testForBudget :: FilePath -> String -> UplcEvaluatorFun ExBudget -> TestTree
    testForBudget dir name e =
        let goldenFilePath = dir </> name <.> "uplc.budget.expected"
            prettyEither (Left l)  = pretty l
            prettyEither (Right r) = pretty r
        in goldenVsDocM
            (name ++ " (budget)")
            goldenFilePath
            (prettyEither <$> getTestedValue e dir)

-- | Turn the expected file content in text to a `UplcProg` unless the expected result
-- is a parse or evaluation error.
expectedToProg :: T.Text -> Either T.Text UplcProg
expectedToProg txt
  | txt == shownEvaluationFailure =
    Left txt
  | txt == shownParseError =
    Left txt
  | otherwise =
    case parseTxt txt of
        Left _  -> Left txt
        Right p -> Right $ void p

-- | Get the tested value. The tested value is either the shown parse or evaluation error,
-- or a `UplcProg`.
getTestedValue ::
    UplcEvaluatorFun res
    -> FilePath
    -> IO (Either T.Text res)
getTestedValue eval dir = do
    inputFile <- findByExtension [".uplc"] dir
    case inputFile of
        [] -> error $ "Input file missing in " <> dir
        _:_:_ -> error $ "More than 1 input files in " <> dir
        [file] -> do
            input <- T.readFile file
            case parseTxt input of
                Left _ -> pure $ Left shownParseError
                Right p -> do
                    case eval (void p) of
                        Nothing   -> pure $ Left shownEvaluationFailure
                        Just prog -> pure $ Right prog

-- | The comparison function used for the golden test.
-- This function checks alpha-equivalence of programs when the output is a program.
compareAlphaEq ::
    Either T.Text UplcProg -- ^ golden value
    -> Either T.Text UplcProg -- ^ tested value
    -> Maybe String
    -- ^ If two values are the same, it returns `Nothing`.
    -- If they are different, it returns an error that will be printed to the user.
compareAlphaEq (Left expectedTxt) (Left actualTxt) =
    if actualTxt == expectedTxt
    then Nothing
    else Just $
        "Test failed, the output failed to parse or evaluate: \n"
        <> T.unpack actualTxt
compareAlphaEq (Right expected) (Right actual) =
    if actual == expected
    then Nothing
    else Just $
        "Test failed, the output was successfully parsed and evaluated, but it isn't as expected. "
        <> "The output program is: \n"
        <> display actual
        <> "\n The output program, with the unique names shown is: \n"
        -- using `show` here so that the unique names will show
        <> show actual
        -- the user can look at the .expected file, but they can't see the unique names
        <> "\n But the expected result, with the unique names shown is: \n"
        <> show expected
compareAlphaEq (Right expected) (Left actualTxt) =
    pure $ "Test failed, the output failed to parse or evaluate: \n"
        <> T.unpack actualTxt
        <> "\n But the expected result, with the unique names shown is: \n"
        <> show expected
compareAlphaEq (Left txt) (Right actual) =
    {- this is to catch the case when the expected program failed to parse because
    our parser doesn't support `data` atm. In this case, if the textual program is the same
    as the actual, the test succeeds. -}
    if txt == display actual then Nothing
    else Just $
        "Test failed, the output was successfully parsed and evaluated, but it isn't as expected. "
        <> "The output program is: "
        <> display actual
        <> ". But the expected result is: "
        <> T.unpack txt

-- | Update the golden file with the tested value. TODO abstract out for other tests.
updateGoldenFile ::
    FilePath -- ^ the path to write the golden file to
    -> Either T.Text UplcProg -> IO ()
updateGoldenFile goldenPath (Left txt) = T.writeFile goldenPath txt
updateGoldenFile goldenPath (Right p)  = T.writeFile goldenPath (display p)

-- | Run the UPLC evaluation tests given an `evaluator` that evaluates UPLC programs.
runUplcEvalTests ::
    UplcEvaluator -- ^ The action to run the input through for the tests.
    -> (FilePath -> Bool)
    -- ^ A function that takes a test name and returns
    -- whether it should labelled as `ExpectedFailure`.
    -> IO ()
runUplcEvalTests eval expectedFailTests = do
    let params = fromJust defaultCostModelParamsForTesting
    tests <-
        discoverTests
            eval
            params
            expectedFailTests
            "test-cases/uplc/evaluation"
    defaultMain $ testGroup "UPLC evaluation tests" [tests]

