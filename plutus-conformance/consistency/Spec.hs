{-| Tests checking that `.flat` files decode to the same AST as the
corresponding textual `.uplc` files and that every `.uplc` file has a
corresponding `.flat` file, and vice-versa.  This will make sure that
we remember to add both formats when we add a new test. -}
module Main (main) where

import Data.ByteString qualified as BS
import Data.Text qualified as T
import Data.Text.IO qualified as T
import PlutusConformance.Common
import PlutusPrelude (display)
import System.Directory
import System.FilePath
  ( dropExtension
  , takeBaseName
  , (<.>)
  , (</>)
  )
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.Golden (findByExtension)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase)
import Test.Tasty.Providers (TestTree)
import Witherable (Witherable (wither))

{-| A list of directories which should be skipped because for one reason or another
    we don't have flat files or don't currently expect the test to pass. -}
skippedConsistencyTests :: [FilePath]
skippedConsistencyTests =
  [ -- The tests in `constant` are supposed to test that the textual parser
    -- parses constants correctly. This doesn't really make sense for `flat`
    -- files, so we skip them.
    "test-cases/uplc/evaluation/builtin/parser"
  , "test-cases/uplc/evaluation/term/parser"
  , -- We skip this test for the time being.  It involves a program with a free
    -- variable, and this will not be detected by the parser but will be detected
    -- by the flat decoder.  It's OK in the main conformance tests because free
    -- variables are detected by deBruijnTerm, which we call before executing the
    -- textual test cases.
    "test-cases/uplc/evaluation/term/var"
  ]

{-| Check that a `.flat` file decodes to the same AST as the textual UPLC
program in the corresponding `.uplc` file. Used for the raw test-case input
files, which are always expected to actually represent a program (any
directory where that's deliberately not the case, eg parser tests, is
skipped entirely -- see `skippedConsistencyTests`). -}
assertFlatMatchesUplc
  :: FilePath
  -- ^ path to the `.uplc` file
  -> FilePath
  -- ^ path to the corresponding `.flat` file
  -> Assertion
assertFlatMatchesUplc uplcFile flatFile = do
  uplcResult <- expectedToProg <$> T.readFile uplcFile
  flatResult <- decodeFlatProg <$> BS.readFile flatFile
  case (uplcResult, flatResult) of
    (Left _, Left _) -> pure () -- both fail to represent a program: fine
    (Right uplcProg, Right flatProg)
      | uplcProg == flatProg -> pure ()
      | otherwise ->
          assertFailure $
            "AST mismatch between "
              <> flatFile
              <> " and "
              <> uplcFile
              <> ".\nDecoded from "
              <> flatFile
              <> ":\n"
              <> display flatProg
              <> "\nParsed from "
              <> uplcFile
              <> ":\n"
              <> display uplcProg
    (Left _, Right flatProg) ->
      assertFailure $
        uplcFile
          <> " does not represent a program, but "
          <> flatFile
          <> " decoded successfully to:\n"
          <> display flatProg
    (Right uplcProg, Left err) ->
      assertFailure $
        flatFile
          <> " failed to decode ("
          <> err
          <> "), but "
          <> uplcFile
          <> " represents the program:\n"
          <> display uplcProg

{-| Check that a `.flat.expected` golden file matches the corresponding
`.uplc.expected` golden file: either both represent the same program (up to
alpha-equivalence), or both record exactly the same failure-reason text (eg
both "evaluation failure") -- see `decodeFlatExpected`. Unlike
`assertFlatMatchesUplc`, a `.flat.expected` file may legitimately record a
failure, using the same failure-reason markers as `.uplc.expected`. -}
assertFlatExpectedMatchesUplcExpected
  :: FilePath
  -- ^ path to the `.uplc.expected` file
  -> FilePath
  -- ^ path to the corresponding `.flat.expected` file
  -> Assertion
assertFlatExpectedMatchesUplcExpected uplcFile flatFile = do
  uplcResult <- expectedToProg <$> T.readFile uplcFile
  flatResult <- decodeFlatExpected <$> BS.readFile flatFile
  case (uplcResult, flatResult) of
    (Left uplcTxt, Left flatTxt)
      | uplcTxt == flatTxt -> pure ()
      | otherwise ->
          assertFailure $
            "Failure reason mismatch: "
              <> uplcFile
              <> " says \""
              <> T.unpack uplcTxt
              <> "\" but "
              <> flatFile
              <> " says \""
              <> T.unpack flatTxt
              <> "\""
    (Right uplcProg, Right flatProg)
      | uplcProg == flatProg -> pure ()
      | otherwise ->
          assertFailure $
            "AST mismatch between "
              <> flatFile
              <> " and "
              <> uplcFile
              <> ".\nDecoded from "
              <> flatFile
              <> ":\n"
              <> display flatProg
              <> "\nParsed from "
              <> uplcFile
              <> ":\n"
              <> display uplcProg
    (Left uplcTxt, Right flatProg) ->
      assertFailure $
        uplcFile
          <> " represents a failure (\""
          <> T.unpack uplcTxt
          <> "\"), but "
          <> flatFile
          <> " decoded successfully to:\n"
          <> display flatProg
    (Right uplcProg, Left flatTxt) ->
      assertFailure $
        flatFile
          <> " represents a failure (\""
          <> T.unpack flatTxt
          <> "\"), but "
          <> uplcFile
          <> " represents the program:\n"
          <> display uplcProg

{-| Walk a file tree (expected to be `test-cases/uplc/evaluation`).  Any
directory (leaf or non-leaf) listed in `skippedDirs` is skipped entirely,
along with everything below it.  For every other test-case directory, this
requires that a `.uplc` file and a `.flat` file exist together or not at
all: if one is present without the other, that's reported as a failing test
(the idea being that this should remind us to add a `.flat` file whenever we
add a new `.uplc` file, and vice versa).  If both are present, we check that
the `.flat` file decodes to the same AST as the `.uplc` file, and likewise
for the `.flat.expected`/`.uplc.expected` pair.  If neither is present but
the directory nonetheless contains golden (`.expected`) files, that's also
reported as a failing test, since it looks like a test case whose input
file(s) got lost or misnamed rather than a directory that was never meant to
hold uplc/flat tests at all. -}
discoverTestcases
  :: [FilePath]
  {-^ Paths, relative to the root of plutus-conformance, of directories to
  skip entirely (along with any subdirectories), eg
  "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger-01" or
  "test-cases/uplc/evaluation/builtin/constant". -}
  -> FilePath
  -- ^ The directory to search for tests.
  -> IO TestTree
discoverTestcases skippedDirs = go
  where
    go dir
      | dir `elem` skippedDirs = pure $ testGroup (takeBaseName dir) []
      | otherwise = do
          let name = takeBaseName dir
          children <- listDirectory dir
          subdirs <- flip wither children $ \child -> do
            let fullPath = dir </> child
            isDir <- doesDirectoryExist fullPath
            pure $ if isDir then Just fullPath else Nothing
          if null subdirs
            then testGroup name <$> leafTests dir
            else testGroup name <$> traverse go subdirs
    leafTests dir = do
      uplcFiles <- findByExtension [".uplc"] dir
      flatFiles <- findByExtension [".flat"] dir
      uplcFile <- case uplcFiles of
        [] -> pure Nothing
        [f] -> pure (Just f)
        _ -> error $ "More than one .uplc file in " <> dir
      flatFile <- case flatFiles of
        [] -> pure Nothing
        [f] -> pure (Just f)
        _ -> error $ "More than one .flat file in " <> dir
      goldenFiles <- findByExtension [".expected"] dir
      case (uplcFile, flatFile) of
        (Nothing, Nothing)
          | null goldenFiles -> pure [] -- not a uplc/flat test-case directory
          | otherwise ->
              -- There are golden files (eg `.uplc.expected`) but no input
              -- file at all: this looks like a test-case directory whose
              -- `.uplc`/`.flat` input got lost or misnamed, not a directory
              -- that was never meant to hold uplc/flat tests.
              pure
                [ testCase "input file exists" . assertFailure $
                    "Directory "
                      <> dir
                      <> " has golden file(s) ("
                      <> show goldenFiles
                      <> ") but no .uplc or .flat input file"
                ]
        (Just u, Just f) ->
          pure
            [ testCase "flat matches uplc" $ assertFlatMatchesUplc u f
            , testCase "flat.expected matches uplc.expected" $
                assertFlatExpectedMatchesUplcExpected (u <.> "expected") (f <.> "expected")
            ]
        (Just u, Nothing) ->
          pure
            [ testCase "flat file exists" . assertFailure $
                "Missing "
                  <> dropExtension u <.> "flat"
                  <> ": every .uplc file must have a corresponding .flat file"
            ]
        (Nothing, Just f) ->
          pure
            [ testCase "uplc file exists" . assertFailure $
                "Missing "
                  <> dropExtension f <.> "uplc"
                  <> ": every .flat file must have a corresponding .uplc file"
            ]

{-| Run the tests that check that every `.uplc` file (outside `skippedDirs`)
has a corresponding `.flat` file (and vice versa), and that `.flat` files
decode to the same AST as their corresponding `.uplc` files. -}
runConsistencyTests
  :: [FilePath]
  {-^ Paths, relative to the root of plutus-conformance, of test-case
  directories to skip entirely. -}
  -> IO ()
runConsistencyTests skippedDirs = do
  tests <- discoverTestcases skippedDirs "test-cases"
  defaultMain $ testGroup "Flat/UPLC decoding tests" [tests]

main :: IO ()
main = runConsistencyTests skippedConsistencyTests
