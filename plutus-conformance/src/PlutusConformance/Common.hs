{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}

{- | Plutus conformance test suite library. -}
module PlutusConformance.Common where

import Control.Lens (traverseOf)
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
import Test.Tasty.Providers
import Text.Megaparsec (SourcePos)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (evaluateCekNoEmit)
import UntypedPlutusCore.Parser qualified as UPLC
import Witherable

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

-- Tells 'tasty' that 'UplcEvaluationTest' "is" a test that can be run,
-- by specifying how to run it and what custom options it might expect.
instance IsTest UplcEvaluationTest where
    run _ MkUplcEvaluationTest{testDir,evaluator} _ = do
        let name = takeBaseName testDir
        input <- T.readFile $ testDir </> name <> ".uplc"
        let parsed = parseTxt input

        expected <- T.readFile $ testDir </> name <> ".uplc.expected"
        let checkContents c | c == expected = pure (testPassed "")
            checkContents c = pure (testFailed (show c))

        case parsed of
            Left _ -> checkContents shownParseError
            Right p -> do
               case evaluator (void p) of
                   Nothing -> checkContents shownEvaluationFailure
                   Just p' -> checkContents (display p')

    testOptions = pure []


{- | The default shown text when a parse error occurs.
We don't want to show the detailed parse errors so that
users of the test suite can produce this expected outputs more easily. -}
shownParseError :: T.Text
shownParseError = "parse error"

-- | The default shown text when evaluation fails.
shownEvaluationFailure :: T.Text
shownEvaluationFailure = "evaluation failure"

-- For UPLC evaluation tests

-- | The default parser to parse the inputs.
parseTxt ::
    T.Text
    -> Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SourcePos)
parseTxt resTxt = runQuoteT $ UPLC.parseProgram resTxt

-- | Our `evaluator` for the UPLC tests is the CEK machine.
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

-- | Run the tests given a `evaluator` that evaluates UPLC programs.
runUplcEvalTests ::
    UplcEvaluator -- ^ The action to run the input through for the tests.
    -> IO ()
runUplcEvalTests evaluator = do
    tests <- discoverTests (\dir -> MkUplcEvaluationTest evaluator dir) "uplc/evaluation"
    defaultMain $ testGroup "UPLC evaluation tests" [tests]

-- Common functions for all tests

-- | Walk a file tree, making test groups for directories with subdirectories,
-- and test cases for directories without.
discoverTests :: IsTest t => (FilePath -> t) -> FilePath -> IO TestTree
discoverTests tester dir = do
    let name = takeBaseName dir
    children <- listDirectory dir
    subdirs <- flip wither children $ \child -> do
        let fullPath = dir </> child
        isDir <- doesDirectoryExist fullPath
        pure $ if isDir then Just fullPath else Nothing
    if null subdirs
    -- no children, this is a test case directory
    then pure $ singleTest name $ tester dir
    -- has children, so it's a grouping directory
    else testGroup name <$> traverse (discoverTests tester) subdirs
