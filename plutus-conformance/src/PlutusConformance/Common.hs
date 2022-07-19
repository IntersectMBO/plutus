{-# LANGUAGE FlexibleInstances    #-}
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
import Test.Tasty.ExpectedFailure
import Test.Tasty.Golden
import Test.Tasty.Golden.Advanced (goldenTest)
import Test.Tasty.Providers
import Text.Megaparsec (SourcePos)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.DeBruijn
import UntypedPlutusCore.Evaluation.Machine.Cek (evaluateCekNoEmit)
import UntypedPlutusCore.Parser qualified as UPLC
import Witherable

-- Common functions for all tests

-- | Walk a file tree, making test groups for directories with subdirectories,
-- and test cases for directories without.
discoverTests :: UplcEvaluator
    -> (FilePath -> Bool)
    -- ^ A function that takes a test name and returns
    -- whether it should labelled as `ExpectedFailure`.
    -> FilePath -- ^ The directory to search for tests.
    -> IO TestTree
discoverTests eval expectedFailureFn dir = do
    let name = takeBaseName dir
    children <- listDirectory dir
    subdirs <- flip wither children $ \child -> do
        let fullPath = dir </> child
        isDir <- doesDirectoryExist fullPath
        pure $ if isDir then Just fullPath else Nothing
    if null subdirs
    -- no children, this is a test case directory
    then do
        goldenFile <- findByExtension [".expected"] dir
        case goldenFile of
            [] -> error $ "Golden file missing in " <> dir --TODO this may mess up the accept opt
            _:_:_ -> error $ "More than 1 golden files in " <> dir
            _ -> do
                let goldenFilePath = head goldenFile
                    mkGoldenTest =
                            goldenTest
                                name -- test name
                                -- get the golden test value
                                (fmap expectedToProg $ T.readFile goldenFilePath)
                                -- get the tested value
                                (getTestedValue eval dir)
                                compareAlphaEq -- comparison function
                                (updateGoldenFile goldenFilePath) -- update the golden file (we don't need to do this)
                -- if the test is one that is expected to fail, mark it so.
                if expectedFailureFn dir
                then pure $ expectFail mkGoldenTest
                -- the test is not one that is expected to fail, make the test tree as usual.
                else pure mkGoldenTest
    -- has children, so it's a grouping directory
    else testGroup name <$> traverse (discoverTests eval expectedFailureFn) subdirs

-- | Update the golden file with the tested value.
updateGoldenFile ::
    FilePath -- ^ the path to write the golden file to
    -> Either T.Text RawTxtOrDebruijnTerm -> IO ()
updateGoldenFile goldenPath (Left txt) = T.writeFile goldenPath txt
updateGoldenFile goldenPath (Right p)  = T.writeFile goldenPath (raw p)

-- | The comparison function used for the golden test.
-- This function checks alpha-equivalence of programs.
compareAlphaEq ::
    Either T.Text RawTxtOrDebruijnTerm -- ^ golden value
    -> Either T.Text RawTxtOrDebruijnTerm -- ^ tested value
    -> IO (Maybe String)
    -- ^ If two values are the same, it returns `Nothing`.
    -- If they are different, it returns an error that will be printed to the user.
compareAlphaEq (Left expectedTxt) (Left actualTxt) =
    if actualTxt == expectedTxt
    then pure Nothing
    else pure $ Just $ "Test failed, the output is: " <> T.unpack actualTxt
compareAlphaEq (Right expected) (Right actual) =
    if inDebruijnTerm actual == inDebruijnTerm expected
    then pure Nothing
    else pure $
        Just $ "Test failed, the output was successfully parsed, but its not as expected. "
        <> "The output program is: "
        <> (display $ raw actual)
        <> "The output program, in Debruijn indexes is:"
        <> (display $ inDebruijnTerm actual)
        -- the user can look at the .expected file, but they can't see it in Debruijn term
        <> ". But the expected result in Debruijn indexes is: "
        <> (display $ inDebruijnTerm expected)
compareAlphaEq (Right expected) (Left actualTxt) =
    pure $ Just $ "Test failed, the output is: "
        <> T.unpack actualTxt
        <> ". But the expected result in Debruijn indexes is: "
        <> (display $ inDebruijnTerm expected)
compareAlphaEq (Left txt) (Right actual) =
    if txt == raw actual then pure Nothing
    else
        pure $ Just $ "Test failed, the output was successfully parsed, but its not as expected. "
            <> "The output program is: "
            <> (display $ raw actual)
            <> ". But the expected result is: "
            <> T.unpack txt

data RawTxtOrDebruijnTerm
    = MkRawTxtOrDebruijnTerm {
        raw              :: T.Text
        , inDebruijnTerm :: UPLC.Term NamedDeBruijn DefaultUni DefaultFun ()
    }

-- | Get the tested value.
getTestedValue ::
    UplcEvaluator
    -> FilePath
    -> IO (Either T.Text RawTxtOrDebruijnTerm)
getTestedValue eval dir = do
    inputFile <- findByExtension [".uplc"] dir
    case inputFile of
        [] -> error $ "Input file missing in " <> dir
        _:_:_ -> error $ "More than 1 input files in " <> dir
        _ -> do
            input <- T.readFile $ head inputFile
            case parseTxt input of
                Left _ -> pure $ Left shownParseError
                Right p -> do
                    case eval (void p) of
                        Nothing                           -> pure $ Left shownEvaluationFailure
                        Just prog@(UPLC.Program () _version tm) -> do
                            case UPLC.deBruijnTerm tm of
                                Left (_ :: UPLC.FreeVariableError) -> pure $ Left shownEvaluationFailure
                                Right dbTm                         ->
                                    pure $ Right $ MkRawTxtOrDebruijnTerm (display prog) dbTm

-- | Turn the expected file content in text to a `UplcProg` in Debruijn unless the expected result
-- is a parse or evaluation error.
expectedToProg :: T.Text -> Either T.Text RawTxtOrDebruijnTerm
expectedToProg txt
  | txt == shownEvaluationFailure =
    Left txt
  | txt == shownParseError =
    Left txt
  | otherwise =
    case parseTxt txt of
        Left _     -> Left txt
        Right p -> -- The evaluator throws if the term has free variables
            case UPLC.deBruijnTerm (UPLC._progTerm (void p)) of
                Left (_ :: UPLC.FreeVariableError) -> Left shownEvaluationFailure
                Right dbTm                         ->
                    Right $ MkRawTxtOrDebruijnTerm txt dbTm

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

-- | The default parser to parse the UPLC program inputs.
parseTxt ::
    T.Text
    -> Either ParserErrorBundle (UPLC.Program Name DefaultUni DefaultFun SourcePos)
parseTxt resTxt = runQuoteT $ UPLC.parseProgram resTxt

-- | Run the UPLC evaluation tests given an `evaluator` that evaluates UPLC programs.
runUplcEvalTests ::
    UplcEvaluator -- ^ The action to run the input through for the tests.
    -> (FilePath -> Bool)
    -> IO ()
runUplcEvalTests eval expectedFailTests = do
    tests <-
        discoverTests
            eval
            expectedFailTests
            "test-cases/uplc/evaluation"
    defaultMain $ testGroup "UPLC evaluation tests" [tests]
