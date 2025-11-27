module Test.Certifier.Executable where

import Data.Char (toUpper)
import Data.List (find, isPrefixOf)
import System.Directory (getCurrentDirectory, removeDirectoryRecursive, setCurrentDirectory)
import System.Exit
import System.FilePath
import System.Process

import Test.Tasty
import Test.Tasty.HUnit

{-| The tests in this file run tests of the uplc certifier. Various
    unoptimised UPLC is fed to the optimiser with the certifier turned
    on, which will then call the Agda decision procedures for each of
    the phases. -}
{-| Run an external executable with some arguments.  This is for use inside
    HUnit Assertions -}

-- TODO(https://github.com/IntersectMBO/plutus-private/issues/1582):
-- this is a mess, makeExampleM uses another function to run the certifier, need to
-- refactor things to introduce less duplication
makeUplcCert :: String -> IO FilePath
makeUplcCert name = do
  let inputFile = fixedPath </> "UPLC" </> name ++ ".uplc"
  let args =
        [ "optimise"
        , "--certify"
        , name
        , "--input"
        , inputFile
        , "--print-mode"
        , "Classic"
        ]
  (exitCode, output, err) <- readProcessWithExitCode "uplc" args ""
  let certDir = find (fstToUpper name `isPrefixOf`) . concatMap words . lines $ output
  case exitCode of
    ExitFailure code ->
      assertFailure $
        "uplc failed with code: "
          <> show code
          <> " and output: "
          <> output
          <> " and error: "
          <> err
    ExitSuccess ->
      case certDir of
        Just certDir' -> pure certDir'
        Nothing ->
          assertFailure $
            "uplc failed to produce a certificate for "
              <> name
              <> " with output: "
              <> output
              <> " and error: "
              <> err

fstToUpper :: String -> String
fstToUpper [] = []
fstToUpper (x : xs) = toUpper x : xs

makeSimpleCertTest :: String -> TestTree
makeSimpleCertTest name =
  testCase name $ do
    dirName <- makeUplcCert name
    removeDirectoryRecursive dirName

-- These come from `uplc example -a`
exampleNames :: [String]
exampleNames =
  [ "succInteger"
  , "unitval"
  , "true"
  , "false"
  , "churchZero"
  , "churchSucc"
  , "overapplication"
  , "factorial"
  , "fibonacci"
  , "NatRoundTrip"
  , "ScottListSum"
  , "IfIntegers"
  , "ApplyAdd1"
  , "ApplyAdd2"
  , "DivideByZero"
  , "DivideByZeroDrop"
  ]

makeExampleM :: String -> IO ExitCode
makeExampleM testname = do
  (_, example, _) <- readProcessWithExitCode "uplc" ["example", "-s", testname] []
  let testNameCert = testname <> "Cert"
      args =
        [ "optimise"
        , "--certify"
        , testNameCert
        , "--print-mode"
        , "Classic"
        ]
  (exitCode, output, err) <- readProcessWithExitCode "uplc" args example
  case exitCode of
    ExitFailure code ->
      assertFailure $
        "uplc failed with code: "
          <> show code
          <> " and output: "
          <> output
          <> " and error: "
          <> err
    ExitSuccess -> do
      let certDir = find (fstToUpper testNameCert `isPrefixOf`) . concatMap words . lines $ output
      case certDir of
        Just certDir' -> do
          removeDirectoryRecursive certDir'
          pure exitCode
        Nothing ->
          assertFailure $
            "uplc failed to produce a certificate for "
              <> testNameCert
              <> " with output: "
              <> output
              <> " and error: "
              <> err

makeExample :: String -> Assertion
makeExample testname = do
  result <- makeExampleM testname
  assertBool
    (testname ++ " fails to certify")
    $ result == ExitSuccess

-- Serialisation tests: run the certifier to make a certificate,
-- then try to load it in Agda.
runAgda :: String -> IO (ExitCode, String)
runAgda file = do
  (exitCode, result, _) <- readProcessWithExitCode "agda-with-stdlib-and-metatheory" [file] []
  return (exitCode, result)

agdaTestCert :: String -> Assertion
agdaTestCert name = do
  certDir <- makeUplcCert name
  oldDir <- getCurrentDirectory
  setCurrentDirectory certDir
  (resCode, resText) <- runAgda ("src" </> fstToUpper name <> ".agda")
  setCurrentDirectory oldDir
  if resCode == ExitSuccess
    then removeDirectoryRecursive certDir
    else assertFailure $ name ++ " creates an invalid certificate: " ++ resText

{-
agdaExampleCert :: String -> Assertion
agdaExampleCert name = do
    _ <- makeExampleM name
    (resCode, resText) <- runAgda "TestCert.agda"
    assertBool ("Example " ++ name
      ++ " creates an invalid certificate: \\n" ++ resText)
      (resCode == ExitSuccess)
-}

-- We were just calling the nested stuff with this constant, so it
-- might as well be constant for now.
fixedPath :: FilePath
fixedPath = "test/certifier/"

srcTests :: [String]
srcTests =
  [ "inc"
  , "len"
  , "MinBS"
  , "AA2-CSE"
  , "forceDelayIfThenElse"
  , "builtinUnparse"
  ]

makeExampleTests :: [String] -> [TestTree]
makeExampleTests = map (\testname -> testCase testname (makeExample testname))

makeSimpleTests :: [String] -> [TestTree]
makeSimpleTests = map $ makeSimpleCertTest

makeSerialisationTests :: [String] -> [TestTree]
makeSerialisationTests = map (\testname -> testCase testname (agdaTestCert testname))

{-
makeSerialisationExampleTests :: [ String ] -> [ TestTree]
makeSerialisationExampleTests = map (\testname -> testCase testname (agdaExampleCert testname))
-}

executableTests :: TestTree
executableTests =
  testGroup
    "certifier executable tests"
    [ -- TODO: tracked by https://github.com/IntersectMBO/plutus-private/issues/1556
      -- testGroup "example serialisation certification"
      --                $ makeSerialisationExampleTests exampleNames
      testGroup "simple certification" $ makeSimpleTests srcTests
    , testGroup "example certification" $ makeExampleTests exampleNames
    , testGroup "serialisation certification" $ makeSerialisationTests srcTests
    ]
