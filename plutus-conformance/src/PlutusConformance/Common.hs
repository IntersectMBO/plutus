{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Plutus conformance test suite library.
module PlutusConformance.Common where

import Data.ByteString qualified as BS
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (Proxy))
import Data.Tagged (Tagged (Tagged))
import Data.Text qualified as T
import Data.Text.IO qualified as T
import PlutusCore.Annotation
import PlutusCore.DeBruijn (fakeNameDeBruijn)
import PlutusCore.Default
  ( DefaultFun
  , DefaultUni
  )
import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
  ( defaultCostModelParamsForTesting
  )
import PlutusCore.Flat
  ( DecodeException
  , unflat
  )
import PlutusCore.Name.Unique (Name)
import PlutusCore.Quote (runQuoteT)
import PlutusPrelude
  ( Pretty (pretty)
  , display
  , void
  )
import System.Directory
import System.FilePath
  ( takeBaseName
  , takeFileName
  , (<.>)
  , (</>)
  )
import Test.Tasty
  ( defaultIngredients
  , includingOptions
  , testGroup
  )
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.Extras (goldenVsDocM)
import Test.Tasty.Golden (findByExtension)
import Test.Tasty.Golden.Advanced (goldenTest)
import Test.Tasty.Options
  ( IsOption (..)
  , OptionDescription (Option)
  , lookupOption
  )
import Test.Tasty.Providers (TestTree)
import Test.Tasty.Runners
  ( defaultMainWithIngredients
  , parseOptions
  )
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

-- Test-case input format

{-| The format of the test-case input files that the tests should be run
against: either the textual `.uplc` representation or the `flat`-encoded
`.flat` representation of the same program.  See `formatExtension`. -}
data Format = Textual | Flat
  deriving stock (Show, Eq)

-- | The filename extension (without the leading dot) used for a given `Format`.
formatExtension :: Format -> String
formatExtension Textual = "uplc"
formatExtension Flat = "flat"

{-| This instance allows `Format` to be used as a `tasty` command-line option
(`--format=uplc` or `--format=flat`), so that users of the test suites can
choose which input format the tests are run against.  The default is `Uplc`. -}
instance IsOption Format where
  defaultValue = Textual
  parseValue s = case s of
    "uplc" -> Just Textual
    "flat" -> Just Flat
    _ -> Nothing
  optionName = Tagged "format"
  optionHelp =
    Tagged
      "The format of the test-case input files to run the tests against: \
      \'textual' (textual UPLC source) or 'flat' (flat-encoded UPLC). \
      \Default: uplc."

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
   contain a single input file, in the given `Format`, whose name matches that
   of the directory. For example, if the `Format` is `UPLC` then the directory
   `modInteger-15` should contain `modInteger-15.uplc`, and that file should
   contain a textual UPLC program; if the `Format` is `Flat` then it should
   instead contain `modInteger-15.flat`, a `flat`-encoded UPLC program.  Note
   that whichever input format is used, the golden files are always named
   `modInteger-15.uplc.expected` (containing the expected output of the
   program) and `modInteger-15.uplc.budget.expected` (containing the expected
   execution budget): the input format only affects how the input program
   itself is obtained, not how the expected results are represented. These
   golden files will be created by the testing machinery if they aren't
   already present.

   Not every test-case directory necessarily has an input file for every
   `Format` yet (for example `.flat` files don't make sense for the tests
   under `test-cases/uplc/evaluation/builtin/constant`, which test the
   handling of constants by the textual parser): such directories are simply
   skipped rather than treated as an error. -}
discoverTests
  :: Format
  -- ^ The format of the test-case input files to run the tests against.
  -> UplcEvaluator
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
discoverTests fmt eval modelParams evaluationFailureExpected budgetFailureExpected =
  go
  where
    ext = formatExtension fmt
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
          -- Check that the directory <dir> contains at most one input file
          -- with the extension for the requested format, and that if it's
          -- present it's called <name>.<ext>, where <name> is the final path
          -- component of <dir>.
          inputFiles <- findByExtension ["." <> ext] dir
          let expectedInputFile = takeFileName dir <.> ext
          case inputFiles of
            [] ->
              -- No input file in this format for this test case: skip it.
              pure $ testGroup name []
            _ : _ : _ -> error $ "More than one ." <> ext <> " file in " <> dir
            [inputFilePath] ->
              if takeFileName inputFilePath /= expectedInputFile
                then
                  error $
                    "Found file "
                      ++ takeFileName inputFilePath
                      ++ " in directory "
                      ++ dir
                      ++ " (expected "
                      ++ expectedInputFile
                      ++ ")"
                else pure $ case eval of
                  UplcEvaluatorWithCosting f ->
                    testGroup
                      name
                      [ testForEval dir inputFilePath (fmap fst . f modelParams)
                      , testForBudget dir inputFilePath (fmap snd . f modelParams)
                      ]
                  UplcEvaluatorWithoutCosting f -> testForEval dir inputFilePath f
        -- has children, so it's a grouping directory
        else testGroup name <$> traverse go subdirs
    -- The base path (without extension) used for the golden files, which are
    -- always named using the `.uplc` extension regardless of the input format.
    goldenBasePath dir = dir </> takeBaseName dir <.> "uplc"
    testForEval :: FilePath -> FilePath -> UplcEvaluatorFun UplcProg -> TestTree
    testForEval dir inputFilePath e =
      let goldenFilePath = goldenBasePath dir <.> "expected"
          test =
            goldenTest
              (takeFileName inputFilePath ++ " (evaluation)")
              -- get the golden test value
              (expectedToProg <$> T.readFile goldenFilePath)
              -- get the tested value
              (getTestedValue fmt e inputFilePath)
              (\x y -> pure $ compareAlphaEq x y) -- comparison function
              (updateGoldenFile goldenFilePath) -- update the golden file
       in possiblyFailingTest (evaluationFailureExpected dir) test
    testForBudget :: FilePath -> FilePath -> UplcEvaluatorFun ExBudget -> TestTree
    testForBudget dir inputFilePath e =
      let goldenFilePath = goldenBasePath dir <.> "budget" <.> "expected"
          prettyEither (Left l) = pretty l
          prettyEither (Right r) = pretty r
          test =
            goldenVsDocM
              (takeFileName inputFilePath ++ " (budget)")
              goldenFilePath
              (prettyEither <$> getTestedValue fmt e inputFilePath)
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

{-| Check whether some text looks like it's meant to be a UPLC program, ie,
whether it begins with `(program` once whitespace and comments (which may
appear before the `(` and/or between the `(` and `program`) are ignored. -}
looksLikeUplcProgram :: T.Text -> Bool
looksLikeUplcProgram t =
  case T.uncons (dropLeadingCommentsAndSpace t) of
    Just ('(', rest) -> "program" `T.isPrefixOf` dropLeadingCommentsAndSpace rest
    _ -> False
  where
    dropLeadingCommentsAndSpace :: T.Text -> T.Text
    dropLeadingCommentsAndSpace s =
      let s' = T.stripStart s
       in if "--" `T.isPrefixOf` s'
            then dropLeadingCommentsAndSpace (T.dropWhile (/= '\n') s')
            else s'

{-| Turn the expected file content in text to a `UplcProg` unless the expected
result is a parse or evaluation error.  We use the same shape-based check as
`getInputProg` (`looksLikeUplcProgram`) to decide whether the content
represents a program at all, rather than just trying to parse it and seeing
whether that fails: this way, things like the literal `"parse error"` and
`"evaluation failure"` markers are recognised as failures without needing to
attempt (and fail) a real parse. -}
expectedToProg :: T.Text -> Either T.Text UplcProg
expectedToProg txt
  | not (looksLikeUplcProgram txt) = Left txt
  | otherwise =
      case parseTxt txt of
        Left _ -> Left txt
        Right p -> Right $ void p

{-| Obtain the input `UplcProg` from a test-case input file in the given
`Format`, either by parsing it (for `textual`) or by `flat`-decoding it (for
`Flat`). Rather than relying on the parser or decoder itself to fail, we check
directly whether the file looks like it's even meant to contain a program: a
`.uplc` file is expected to begin with `(program` (once any leading
whitespace and comments are ignored: see `looksLikeUplcProgram`), and a
`.flat` file is expected to be non-empty. If a file doesn't meet this
expectation, we treat it as `shownParseError` without attempting to
parse or decode it. Otherwise, we go ahead and parse/decode it to get the
actual program (this may still fail, for example if the program contains an
ill-formed constant). -}
getInputProg :: Format -> FilePath -> IO (Either T.Text UplcProg)
getInputProg Textual file = do
  input <- T.readFile file
  pure $
    if looksLikeUplcProgram input
      then case parseTxt input of
        Left _ -> Left shownParseError
        Right p -> Right $ void p
      else Left shownParseError
getInputProg Flat file = do
  input <- BS.readFile file
  pure $
    if BS.null input
      then Left shownParseError
      else case decodeFlatProg input of
        -- This is a bit messy in order to deal with an edge case.  If a
        -- .uplc file contains a free variable then parsing will succeed
        -- but evaluation will fail, whereas a free variable in a .flat
        -- file will cause decdoing to fail.  We want to get the same
        -- mesage in both cases because they have to agree with the
        -- expected budget file, which will contatin "evaluation failed".
        -- Perhaps the budget file should just say "error" in that case
        -- without trying to distinguish parse errors and evaluation errors.
        Left _ -> Left shownEvaluationFailure
        Right p -> Right p

{-| Get the tested value from a test-case input file in the given `Format`.
The tested value is either the shown parse error or evaluation error, or a
`res`. -}
getTestedValue
  :: Format
  -> UplcEvaluatorFun res
  -> FilePath
  -> IO (Either T.Text res)
getTestedValue fmt eval file = do
  inputProg <- getInputProg fmt file
  pure $ case inputProg of
    Left err -> Left err
    Right p ->
      case eval p of
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
programs.  By default the tests are run against the textual `.uplc` test-case
files, but passing `--format=flat` on the command line makes them run
against the `flat`-encoded `.flat` files instead (see `Format`). -}
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
      ingredients = includingOptions [Option (Proxy :: Proxy Format)] : defaultIngredients
  -- Parse the command-line options (in particular `--format`) up front, since
  -- the choice of format determines which input files `discoverTests` looks
  -- for when it builds the test tree.
  opts <- parseOptions ingredients (testGroup "" [])
  let fmt = lookupOption opts :: Format
  tests <-
    discoverTests
      fmt
      eval
      params
      expectedFailTests
      expectedBudgetFailTests
      "test-cases/uplc/evaluation"
  defaultMainWithIngredients ingredients $ testGroup "UPLC evaluation tests" [tests]

-- Flat/UPLC decoding conformance tests

{-| Turn a `Program` using de Bruijn-indexed variables (as decoded from a
`.flat` file) into the `Name`-based representation used elsewhere in this
module, so that it can be compared with a program obtained by parsing a
textual `.uplc` file. -}
unDeBruijnProgram
  :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
  -> Either UPLC.FreeVariableError UplcProg
unDeBruijnProgram (UPLC.Program ann ver t) =
  runQuoteT (UPLC.Program ann ver <$> UPLC.unDeBruijnTerm t)

{-| Decode a flat-encoded UPLC program.  We use the `UnrestrictedProgram`
wrapper so that the decoding doesn't reject programs on the grounds of using
builtins or term constructs which are unavailable in the version declared by
the program: we just want to know whether the bytes decode to the same AST as
the textual program that they're supposed to correspond to, not whether
they're a valid on-chain script. -}
decodeFlatProg :: BS.ByteString -> Either String UplcProg
decodeFlatProg bs =
  case decoded of
    Left err -> Left $ show err
    Right (UPLC.UnrestrictedProgram dbProg) ->
      case unDeBruijnProgram (UPLC.programMapNames fakeNameDeBruijn dbProg) of
        Left err -> Left $ show err
        Right prog -> Right prog
  where
    decoded
      :: Either
           DecodeException
           (UPLC.UnrestrictedProgram UPLC.DeBruijn DefaultUni DefaultFun ())
    decoded = unflat bs
