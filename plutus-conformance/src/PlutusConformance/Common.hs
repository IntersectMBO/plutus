{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Plutus conformance test suite library.
module PlutusConformance.Common where

import Control.Monad.Except (runExcept)
import Data.ByteString qualified as BS
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (Proxy))
import Data.Tagged (Tagged (Tagged))
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
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
  , flat
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
  , defaultMainWithIngredients
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
import Test.Tasty.Runners (parseOptions)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Parser qualified as UPLC
import Witherable (Witherable (wither))

-- Common functions for all tests

{-| The text shown when a file fails to parse or decode.  We don't want to
show the detailed errors so that users of the test suite can produce the
expected output more easily. This is used in .uplc.expected and .budget.expected
files. -}
shownParseError :: T.Text
shownParseError = "parse/decode error"

{-| The text shown when evaluation fails.  This is used in .uplc.expected and
.budget.expected files. -}
shownEvaluationFailure :: T.Text
shownEvaluationFailure = "evaluation failure"

{-| The default parser to parse UPLC program inputs.
FIXME: unlike the flat decoder, this does not detect free variables: they will
only be detected if/when we deBruijnify the program. -}
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
(`--format=textual` or `--format=flat`), so that users of the test suites can
choose which input format the tests are run against.  The default is `uplc`. -}
instance IsOption Format where
  defaultValue = Textual
  parseValue s = case s of
    "textual" -> Just Textual
    "flat" -> Just Flat
    _ -> Nothing
  optionName = Tagged "format"
  optionHelp =
    Tagged
      "The format of the test-case input files to run the tests against: \
      \'textual' (textual UPLC source) or 'flat' (flat-encoded UPLC). \
      \Default: textual."

-- UPLC evaluation test functions

-- A type to contain a result or one of several kinds of failure
data EvaluationResult res = BadMachineParameters | DecodeError | EvalFailure | EvalSuccess res
  deriving stock (Functor)

-- convenience type synonym
type UplcEvaluatorFun res = UplcProg -> EvaluationResult res

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

{-| Directories under which no `.flat` input files are expected and hence
shouldn't lead to errors.  These test the textual parser's handling of
constants, and there are generally no `flat` equivalents for these tests. This
applies to the directory itself and everything below it. -}
dirsWithNoFlatFiles :: [FilePath]
dirsWithNoFlatFiles =
  [ "test-cases/uplc/evaluation/builtin/parser"
  , "test-cases/uplc/evaluation/term/parser"
  ]

{-| Walk a file tree, making test groups for directories with subdirectories,
   and test cases for directories without.  We expect every test directory to
   contain a single input file, in the given `Format`, whose name matches that
   of the directory. For example, if the `Format` is `UPLC` then the directory
   `modInteger-15` should contain `modInteger-15.uplc`, and that file should
   contain a textual UPLC program; if the `Format` is `Flat` then it should
   instead contain `modInteger-15.flat`, a `flat`-encoded UPLC program.  The
   evaluation golden file is named to match: `modInteger-15.uplc.expected`
   for `Textual`, or `modInteger-15.flat.expected` for `Flat`.  The budget
   golden file, however, is always `modInteger-15.budget.expected`
   regardless of format, since there's no per-format budget convention (the
   budget only depends on the AST, not on how it was obtained). These golden
   files will be created by the testing machinery if they aren't already
   present.

   Every test-case directory is expected to have an input file for the requested
   `Format`; a missing input file is treated as an error, except under the
   directories listed in `dirsWithNoFlatFiles`, where (in `Flat` mode only) no
   `.flat` files is expected and the directory is skipped instead (for example
   `.flat` files don't make sense for the tests under
   `test-cases/uplc/evaluation/builtin/parser`, which test the handling of
   constants by the textual parser). -}
discoverTests
  :: Format
  -- ^ The format of the test-case input files to run the tests against (.uplc or .flat).
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
  go False
  where
    ext = formatExtension fmt
    go flatNotExpected dir = do
      let name = takeBaseName dir
          flatNotExpected' = flatNotExpected || dir `elem` dirsWithNoFlatFiles
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
              if fmt == Flat && flatNotExpected'
                then -- No `.flat` file for this test case, but that's expected here: skip it.
                  pure $ testGroup name []
                else error $ "Input file " ++ expectedInputFile ++ " missing in " ++ dir
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
        else testGroup name <$> traverse (go flatNotExpected') subdirs
    -- The names of all of the golden files begin with the name of the directory.
    goldenBasePath dir = dir </> takeBaseName dir
    testForEval :: FilePath -> FilePath -> UplcEvaluatorFun UplcProg -> TestTree
    testForEval dir inputFilePath e =
      let goldenFilePath = goldenBasePath dir <.> ext <.> "expected"
          test =
            goldenTest
              (takeFileName inputFilePath ++ " (evaluation)")
              -- get the golden test value
              (getExpectedProg fmt goldenFilePath)
              -- get the tested value
              (getTestedValue fmt e inputFilePath)
              (\x y -> pure $ compareAlphaEq x y) -- comparison function
              (updateGoldenFile fmt goldenFilePath) -- update the golden file
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
appear before the `(` and/or between the `(` and `program`, as `--` line
comments or `{\- -\}` block comments -- possibly nested, matching the real
lexer's `whitespace` parser in "PlutusCore.Parser.ParserCommon" -- are
ignored). -}
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
            else case T.stripPrefix "{-" s' of
              Just rest -> dropLeadingCommentsAndSpace (dropBlockComment 1 rest)
              Nothing -> s'
    -- Skip past the remainder of a block comment which is already open to
    -- the given nesting `depth`, ie, past the point where we've just
    -- consumed the opening `{-`. Mirrors `Lex.skipBlockCommentNested "{-"
    -- "-}"`. If the comment is unterminated, we just give up and return the
    -- empty text rather than looping forever.
    dropBlockComment :: Int -> T.Text -> T.Text
    dropBlockComment 0 s = s
    dropBlockComment depth s
      | Just rest <- T.stripPrefix "{-" s = dropBlockComment (depth + 1) rest
      | Just rest <- T.stripPrefix "-}" s = dropBlockComment (depth - 1) rest
      | Just (_, rest) <- T.uncons s = dropBlockComment depth rest
      | otherwise = s

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

{-| Decode the content of a `.flat.expected` golden file.  A `.flat.expected`
file records either a successful evaluation result (as `flat`-encoded
bytes) or a failure (as the UTF8-encoded text of `shownParseError` or
`shownEvaluationFailure`) -- exactly mirroring the `.uplc.expected`
convention (see `expectedToProg`), rather than the old convention of an
empty file standing in for "some failure, reason unspecified". We check for
the text markers first (a valid flat encoding could coincidentally also be
valid UTF8, but it will essentially never happen to be the exact text of
one of the two markers).

If the content is neither a recognised failure marker nor a valid flat
encoding (for example because the golden file is empty, using the old
convention, or has been corrupted), we don't fail outright: instead we
return `Left` with the flat decoder's error text as the "expected" reason.
This will essentially never match a real tested value (which is always
either a real program or exactly `shownParseError`/`shownEvaluationFailure`),
so it surfaces as an ordinary golden-mismatch test failure -- visible on a
normal run, and fixable with `--accept` like any other outdated golden file
(which is how the old empty-file goldens get migrated to the new
convention), rather than a special-cased crash. -}
decodeFlatExpected :: BS.ByteString -> Either T.Text UplcProg
decodeFlatExpected input =
  case TE.decodeUtf8' input of
    Right txt
      | txt == shownParseError || txt == shownEvaluationFailure -> Left txt
    _ -> case decodeFlatProg input of
      Right p -> Right p
      Left err -> Left $ T.pack err

{-| Obtain the expected `UplcProg` from a golden `.expected` file in the given
`Format`: parsed as text for `Textual` (via `expectedToProg`), or decoded
via `decodeFlatExpected` for `Flat`. -}
getExpectedProg :: Format -> FilePath -> IO (Either T.Text UplcProg)
getExpectedProg Textual file = expectedToProg <$> T.readFile file
getExpectedProg Flat file = decodeFlatExpected <$> BS.readFile file

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
        Left _ -> Left shownParseError
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
        BadMachineParameters -> Left shownEvaluationFailure -- questionable, but this should never happen,
        DecodeError -> Left shownParseError
        EvalFailure -> Left shownEvaluationFailure
        EvalSuccess prog -> Right prog

{-| The comparison function used for the golden test.
This function checks alpha-equivalence of programs when the output is a program.
Both `Textual` and `Flat` golden values now record the failure reason precisely
(see `decodeFlatExpected`), so in both cases we require it to match. -}
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

{-| Update the golden file with the tested value, in the given `Format`: as
text for `Textual` (unchanged from before), or, for `Flat`, as `flat`-encoded
bytes on success or the UTF8-encoded failure-reason text on failure (see
`decodeFlatExpected`).
TODO abstract out for other tests. -}
updateGoldenFile
  :: Format
  -> FilePath
  -- ^ the path to write the golden file to
  -> Either T.Text UplcProg
  -> IO ()
updateGoldenFile Textual goldenPath (Left txt) = T.writeFile goldenPath txt
updateGoldenFile Textual goldenPath (Right p) = T.writeFile goldenPath (display p)
updateGoldenFile Flat goldenPath (Left txt) = BS.writeFile goldenPath (TE.encodeUtf8 txt)
updateGoldenFile Flat goldenPath (Right p) = BS.writeFile goldenPath (encodeFlatProg p)

{-| A golden test that is never actually run: it exists only so that it can be
passed to `parseOptions` to make tasty register the `Golden` test provider's
own options (`--accept`, `--no-create`, `--size-cutoff`, `--delete-output`)
before the real test tree (which needs the parsed `--format` option to be
built in the first place) exists. See the comment in `runUplcEvalTests`. -}
representativeGoldenTest :: TestTree
representativeGoldenTest =
  goldenTest
    "representative golden test (for option discovery only)"
    (pure ())
    (pure ())
    (\_ _ -> pure Nothing)
    (\_ -> pure ())

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
  {- Parse the command-line options (in particular `--format`) up front, since the
  choice of format determines which input files `discoverTests` looks for when
  it builds the test tree. We can't parse against the real test tree (building
  it requires knowing the format first), but we can't parse against an empty
  tree either: tasty only recognises a golden test's own options (`--accept`,
  `--no-create`, etc, contributed by the `Golden` provider's `testOptions`) if a
  test using that provider appears somewhere in the tree being parsed (see
  `treeOptions`). So we parse against a tree containing one representative
  golden test purely so that those options are registered; it's never actually
  run. -}
  opts <- parseOptions ingredients (testGroup "" [representativeGoldenTest])
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

{-| Encode a `UplcProg` as `flat` bytes: the inverse of `decodeFlatProg`.
Converts the program's names to de Bruijn indices first (that's the
representation `flat` actually encodes), then encodes it via the same
`UnrestrictedProgram` wrapper `decodeFlatProg` uses, for the same reason
(avoiding rejecting programs on the grounds of builtins/term constructs
unavailable in the declared version). Used to write `.flat.expected` golden
files when accepting a `Flat`-format test result. -}
encodeFlatProg :: UplcProg -> BS.ByteString
encodeFlatProg (UPLC.Program ann ver t) =
  case runExcept (UPLC.deBruijnTerm t) of
    -- Programs written to a golden file are always closed (they come from a
    -- successful evaluation), so this should never actually happen.
    Left (err :: UPLC.FreeVariableError) -> error $ "encodeFlatProg (deBruijnTerm): " <> show err
    Right namedDbTerm ->
      flat $
        UPLC.UnrestrictedProgram $
          UPLC.programMapNames UPLC.unNameDeBruijn (UPLC.Program ann ver namedDbTerm)
