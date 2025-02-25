{- | The tests in this file run tests of the uplc certifier. Various
    unoptimised UPLC is fed to the optimiser with the certifier turned
    on, which will then call the Agda decision procedures for each of
    the phases. -}

module Main (main) where

import Data.Text qualified as T (Text, dropEnd, pack, takeWhileEnd, unpack)
import GHC.IO.Encoding (setLocaleEncoding)
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

makeGoldenUplcCert :: [ String ] -> String -> TestTree
makeGoldenUplcCert path name = do
    let inputfile = foldr (</>) ("UPLC" </> name ++ ".uplc") path
    let goldenfile = foldr (</>) ("Golden" </> name ++ ".golden") path
    let args = ["optimise", "--certify", "TestCert",
                "--input", inputfile,
                "--print-mode", "Classic"]
    let result = runProg "uplc" args []
    goldenVsTextM name goldenfile result

-- These come from `uplc example -a` but there are a couple of failing tests which are omitted.
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
    (testname ++ " successfully certifies: " ++ T.unpack lastLine)
    $ "The compilation was successfully certified." == lastLine

-- We were just calling the nested stuff with this constant, so it
-- might as well be constant for now.
fixedPath :: [ String ]
fixedPath = ["test", "certifier"]

srcTests :: [ String ]
srcTests =
  [ "inc"
  -- , len
  ]

-- These run but the certifier says "no"
rejectedTests :: [String]
rejectedTests =
  [

  ]

makeExampleTests :: [ String ] -> [ TestTree ]
makeExampleTests = map (\testname -> testCase testname (makeExample testname))

makeTestTree :: [ String ] -> [ TestTree ]
makeTestTree = map $ makeGoldenUplcCert fixedPath

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain $
    testGroup "Certification"
    [ testGroup "simple certification"  $ makeTestTree srcTests
    , testGroup "example certification"  $ makeExampleTests exampleNames
    , testGroup "rejected certification"  $ makeTestTree rejectedTests
    ]
