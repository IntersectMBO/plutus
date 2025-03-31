{- | The tests in this file run tests of the uplc certifier. Various
    unoptimised UPLC is fed to the optimiser with the certifier turned
    on, which will then call the Agda decision procedures for each of
    the phases. -}

module Main (main) where

import Data.Text qualified as T (Text, dropEnd, pack, takeWhileEnd, unpack)
import GHC.IO.Encoding (setLocaleEncoding)
import Paths_plutus_metatheory qualified as Paths_plutus_metatheory
import System.Exit
import System.FilePath
import System.IO
import System.Process
import Test.Tasty
import Test.Tasty.HUnit

import Test.Tasty.Extras (goldenVsTextM)

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
  plutusMetatheoryAgdaLibSrc <- Paths_plutus_metatheory.getDataFileName "src"
  (exitCode, result, _) <- 
    readProcessWithExitCode 
      "/nix/store/3vp8iaxwx34rfizwrj3sx3jhj9l3an2q-agda/bin/agda" 
      ["--with-compiler=/nix/store/njrn9ry2hc82jk5wfvj6ld5dj01l41f8-ghc-shell-for-packages-ghc-9.6.6-env/bin/ghc", file] [] 
      -- [ "-i" ++ plutusMetatheoryAgdaLibSrc, "-i/nix/store/j56804kxj67326j0llc3isrr8njxqlw3-standard-library-2.1.1/src", file ] []
  return (exitCode, result)

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
