module Test.Certifier.Executable where

import Data.Char (toUpper)
import Data.List (subsequences, (\\))
import Data.Text qualified as T (Text, dropEnd, pack, takeWhileEnd, unpack)
import System.Directory (getCurrentDirectory, listDirectory, setCurrentDirectory)
import System.Exit
import System.FilePath
import System.Process

import Test.Tasty
import Test.Tasty.Extras (goldenVsTextM)
import Test.Tasty.HUnit

{- | The tests in this file run tests of the uplc certifier. Various
    unoptimised UPLC is fed to the optimiser with the certifier turned
    on, which will then call the Agda decision procedures for each of
    the phases. -}

{- | Run an external executable with some arguments.  This is for use inside
    HUnit Assertions -}
runProg :: String -> [String] -> String -> IO T.Text
runProg prog args stdin' = do
  (exitCode, output, err) <- readProcessWithExitCode prog args stdin'
  case exitCode of
    ExitFailure _ -> assertFailure $ prog ++ " failed: " ++ err
    ExitSuccess   -> pure ()
  return $ T.pack output

makeUplcCert :: [ String ] -> String -> IO (T.Text, FilePath)
makeUplcCert path name = do
    let inputfile = foldr (</>) ("UPLC" </> name ++ ".uplc") path
    let args = ["optimise", "--certify", "TestCert",
                "--input", inputfile,
                "--print-mode", "Classic"]
    curDir <- getCurrentDirectory
    beforeFiles <- listDirectory curDir
    res <- runProg "uplc" args []
    afterFiles <- listDirectory curDir
    case afterFiles \\ beforeFiles of
      [certDir] -> pure (res, certDir)
      _ -> assertFailure $ "Expected a single new directory, but got: "
        ++ show afterFiles ++ " \\ " ++ show beforeFiles

makeGoldenUplcCert :: [ String ] -> String -> TestTree
makeGoldenUplcCert path name = do
    let goldenfile = foldr (</>) ("Golden" </> name ++ ".golden") path
        result = fst <$> makeUplcCert path name
    goldenVsTextM name goldenfile result

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

makeExampleM :: String -> IO T.Text
makeExampleM testname = do
  example <- runProg "uplc" ["example", "-s", testname] []
  let args = ["optimise", "--certify", "TestCert",
                "--print-mode", "Classic"]
  runProg "uplc" args (T.unpack example)

makeExample :: String -> Assertion
makeExample testname = do
  result <- T.unpack <$> makeExampleM testname
  assertBool
    (testname ++ " fails to certify")
    $ "The compilation was successfully certified." `elem` subsequences result

-- Serialisation tests: run the certifier to make a certificate,
-- then try to load it in Agda.
runAgda :: String -> IO (ExitCode, String)
runAgda file = do
  (exitCode, result, _) <- readProcessWithExitCode "agda-with-stdlib-and-metatheory" [file] []
  return (exitCode, result)


agdaTestCert :: [ String ] -> String -> Assertion
agdaTestCert path name = do
    (_, certDir) <- makeUplcCert path name
    setCurrentDirectory (certDir </> "src")
    (resCode, resText) <- runAgda "TestCert.agda"
    assertBool (name ++ " creates an invalid certificate:" ++ resText) (resCode == ExitSuccess)
  where
    toUpperFirst (x:xs) = toUpper x : xs

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
fixedPath :: [ String ]
fixedPath = ["test", "certifier"]

srcTests :: [ String ]
srcTests =
  [ "inc"
  -- TODO: This is currently failing to certify. This will be fixed
  -- after the PR that covers counter example tracing.
  -- Tracked by https://github.com/IntersectMBO/plutus-private/issues/1555.
  -- , "len"
  , "MinBS"
  , "AA2-CSE"
  ]

makeExampleTests :: [ String ] -> [ TestTree ]
makeExampleTests = map (\testname -> testCase testname (makeExample testname))

makeTestTree :: [ String ] -> [ TestTree ]
makeTestTree = map $ makeGoldenUplcCert fixedPath

makeSerialisationTests :: [ String ] -> [ TestTree]
makeSerialisationTests = map (\testname -> testCase testname (agdaTestCert fixedPath testname))

{-
makeSerialisationExampleTests :: [ String ] -> [ TestTree]
makeSerialisationExampleTests = map (\testname -> testCase testname (agdaExampleCert testname))
-}

executableTests :: TestTree
executableTests =
  testGroup "certifier executable tests"
    [
    -- TODO: tracked by https://github.com/IntersectMBO/plutus-private/issues/1556
    -- testGroup "example serialisation certification"
    --                $ makeSerialisationExampleTests exampleNames
    testGroup "simple certification"  $ makeTestTree srcTests
    , testGroup "example certification"  $ makeExampleTests exampleNames
    , testGroup "serialisation certification"  $ makeSerialisationTests srcTests
    ]
