{- | The tests in this file run tests of the uplc certifier. Various
    unoptimised UPLC is fed to the optimiser with the certifier turned
    on, which will then call the Agda decision procedures for each of
    the phases. -}

module Main (main) where

import Data.Text qualified as T (Text, dropEnd, pack, takeWhileEnd, unpack)
import GHC.IO.Encoding (setLocaleEncoding)
import Paths_plutus_metatheory qualified as Paths_plutus_metatheory
import System.Environment qualified as Env
import System.Exit
import System.FilePath
import System.IO qualified as IO
import System.Process
import Test.Tasty
import Test.Tasty.Extras (goldenVsTextM)
import Test.Tasty.HUnit

{- | Run an external executable with some arguments.  This is for use inside
    HUnit Assertions -}
runProg :: String -> [String] -> String -> IO T.Text
runProg prog args stdin' = do
  (exitCode, output, err) <- readProcessWithExitCode prog args stdin'
  case exitCode of
    ExitFailure _ -> assertFailure $ prog ++ " failed: " ++ err
    ExitSuccess   -> pure ()
  return $ T.pack output

makeUplcCert :: [ String ] -> String -> IO T.Text
makeUplcCert path name = do
    let inputfile = foldr (</>) ("UPLC" </> name ++ ".uplc") path
    let args = ["optimise", "--certify", "TestCert",
                "--input", inputfile,
                "--print-mode", "Classic"]
    runProg "uplc" args []

makeGoldenUplcCert :: [ String ] -> String -> TestTree
makeGoldenUplcCert path name = do
    let goldenfile = foldr (</>) ("Golden" </> name ++ ".golden") path
    let result = makeUplcCert path name
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
  result <- makeExampleM testname
  let lastLine = T.takeWhileEnd (/='\n') $ T.dropEnd 1 result
  assertBool
    (testname ++ " fails to certify: " ++ T.unpack lastLine)
    $ "The compilation was successfully certified." == lastLine

-- Serialisation tests: run the certifier to make a certificate,
-- then try to load it in Agda.
runAgda :: String -> IO (ExitCode, String)
runAgda file = do
  -- setupAgdaEnv
  (exitCode, result, _) <- readProcessWithExitCode "agda" [file] []
  return (exitCode, result)
  -- where
  --   setupAgdaEnv :: IO ()
  --   setupAgdaEnv = do
  --     tempDir <- Dir.createTempDirectory "/tmp" "agda_temp"
  --     let defaultsFile = tempDir </> "defaults"
  --     let librariesFile = tempDir </> "libraries"
  --     metatheoryAgdaLib <- Paths_plutus_metatheory.getDataFileName "plutus-metatheory.agda-lib"
  --     agdaStdlib <- Env.getEnv "AGDA_STDLIB"
  --     IO.writeFile librariesFile (metatheoryAgdaLib <> "\n" <> agdaStdlib)
  --     IO.writeFile defaultsFile "plutus-metatheory\nstandard-library-2.1.1\n"
  --     Env.setEnv "AGDA_DIR" tempDir


agdaTestCert :: [ String ] -> String -> Assertion
agdaTestCert path name = do
    _ <- makeUplcCert path name
    (resCode, resText) <- runAgda "TestCert.agda"
    assertBool (name ++ " creates an invalid certificate:" ++ resText) (resCode == ExitSuccess)

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
  -- , "len"
    , "MinBS"
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

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain $
    testGroup "Certification"
    [ testGroup "simple certification"  $ makeTestTree srcTests
    , testGroup "example certification"  $ makeExampleTests exampleNames
    , testGroup "serialisation certification"  $ makeSerialisationTests srcTests
    --, testGroup "example serialisation certification"
    --                $ makeSerialisationExampleTests exampleNames
    ]
