{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}

{- | Plutus conformance test suite library. -}
module PlutusConformance.Common where

import Control.Lens (traverseOf)
import Data.Proxy (Proxy (Proxy))
import Data.Text qualified as T
import Data.Text.IO qualified as T
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import PlutusCore.Name (Name)
import PlutusCore.Quote (runQuoteT)
import PlutusPrelude
import System.Directory
import System.FilePath (takeBaseName, (</>))
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.ExpectedFailure
import Test.Tasty.Options
import Test.Tasty.Providers
import Text.Megaparsec (SourcePos)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (evaluateCekNoEmit)
import UntypedPlutusCore.Parser qualified as UPLC
import Witherable

-- Common functions for all tests

-- | Walk a file tree, making test groups for directories with subdirectories,
-- and test cases for directories without.
discoverTests :: IsTest t =>
    (FilePath -> t)
    -> (String -> Bool)
    -- ^ A function that takes a test name and returns
    -- whether it should labelled as `ExpectedFailure`.
    -> FilePath -- ^ The directory to search for tests.
    -> IO TestTree
discoverTests tester expectedFailureFn dir = do
    let name = takeBaseName dir
    children <- listDirectory dir
    subdirs <- flip wither children $ \child -> do
        let fullPath = dir </> child
        isDir <- doesDirectoryExist fullPath
        pure $ if isDir then Just fullPath else Nothing
    if null subdirs
    -- no children, this is a test case directory
    then
        -- if the test is one that is expected to fail, mark it so.
        if expectedFailureFn name then
            pure $ expectFail $ singleTest name $ tester dir
        -- the test is not one that is expected to fail, make the test tree as usual.
        else pure $ singleTest name $ tester dir
    -- has children, so it's a grouping directory
    else testGroup name <$> traverse (discoverTests tester expectedFailureFn) subdirs

-- | A test `option` to accept the test results as the expected results.
-- This is basically the same option as 'tasty-golden' uses, but it's not
-- worth a dependency just to reuse the tiny datatype.
-- Set like other tasty options with --test-options, e.g.
-- cabal test plutus-conformance --test-options=--accept
newtype AcceptTests = AcceptTests Bool
  deriving stock (Eq, Ord, Typeable)
instance IsOption AcceptTests where
  defaultValue = AcceptTests False
  parseValue = fmap AcceptTests . safeReadBool
  optionName = return "accept"
  optionHelp = return "Accept current results of tests"
  optionCLParser = flagCLParser Nothing (AcceptTests True)

-- | Checks an expected file against actual computed contents.
checkExpected :: AcceptTests -> FilePath -> T.Text -> IO Result
checkExpected (AcceptTests accept) expectedFile actual = do
    expectedExists <- doesFileExist expectedFile
    if expectedExists
    then do
        expected <- T.readFile expectedFile
        if actual == expected
        -- matched
        then pure (testPassed "")
        else
            -- didn't match
            if accept
            then do
                T.writeFile expectedFile actual
                pure $ testPassed "Unexpected output, accepted it"
            else pure $ testFailed $ "Unexpected output:" ++ show actual
    else if accept
        then do
            T.writeFile expectedFile actual
            pure $ testPassed "Expected file did not exist, created it"
        else pure $ testFailed $ "Expected file did not exist:" ++ show expectedFile

{- | The default shown text when a parse error occurs.
We don't want to show the detailed parse errors so that
users of the test suite can produce the expected output more easily. -}
shownParseError :: T.Text
shownParseError = "parse error"

-- | The default shown text when evaluation fails.
shownEvaluationFailure :: T.Text
shownEvaluationFailure = "evaluation failure"

-- UPLC evaluation test functions

type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

type UplcEvaluator = UplcProg -> Maybe UplcProg

-- | A UPLC evaluation test suite.
data UplcEvaluationTest =
    MkUplcEvaluationTest {
       -- | The evaluator function to use for the test.
       evaluator :: UplcEvaluator
       -- | The test directory in which the test files are located.
       , testDir :: FilePath
    }

-- | Our `evaluator` for the Haskell UPLC tests is the CEK machine.
evalUplcProg :: UplcEvaluator
evalUplcProg = traverseOf UPLC.progTerm eval
  where
    eval t = do
        -- The evaluator throws if the term has free variables
        case UPLC.deBruijnTerm t of
            Left (_ :: UPLC.FreeVariableError) -> Nothing
            Right _                            -> Just ()
        case evaluateCekNoEmit defaultCekParameters t of
            Left _     -> Nothing
            Right prog -> Just prog

-- Tells 'tasty' that 'UplcEvaluationTest' "is" a test that can be run,
-- by specifying how to run it and what custom options it might expect.
instance IsTest UplcEvaluationTest where
    run opts MkUplcEvaluationTest{testDir,evaluator} _ = do
        let name = takeBaseName testDir
            expectedFile = testDir </> name <> ".uplc.expected"
            check = checkExpected (lookupOption opts) expectedFile

        input <- T.readFile $ testDir </> name <> ".uplc"
        let parsed = parseTxt input

        case parsed of
            Left _ -> check shownParseError
            Right p -> do
               case evaluator (void p) of
                   Nothing -> check shownEvaluationFailure
                   Just p' -> check (display p')

    testOptions = pure [Option (Proxy :: Proxy AcceptTests)]

-- | The default parser to parse the UPLC program inputs.
parseTxt ::
    T.Text
    -> Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SourcePos)
parseTxt resTxt = runQuoteT $ UPLC.parseProgram resTxt

-- | Run the UPLC evaluation tests given an `evaluator` that evaluates UPLC programs.
runUplcEvalTests ::
    UplcEvaluator -- ^ The action to run the input through for the tests.
    -> [String] -- ^ The list of tests that are to be labelled as `ExpectedFailure`.
    -> IO ()
runUplcEvalTests evaluator expectedFailTests = do
    tests <-
        discoverTests
            (\dir -> MkUplcEvaluationTest evaluator dir)
            (flip elem expectedFailTests)
            "test-cases/uplc/evaluation"
    defaultMain $ testGroup "UPLC evaluation tests" [tests]
