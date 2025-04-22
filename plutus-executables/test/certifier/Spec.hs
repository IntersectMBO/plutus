{- | The tests in this file run tests of the uplc certifier. Various
    unoptimised UPLC is fed to the optimiser with the certifier turned
    on, which will then call the Agda decision procedures for each of
    the phases. -}

module Main (main) where

import AgdaTrace (mkAgdaTrace)
import Data.Text qualified as T (Text, dropEnd, pack, takeWhileEnd, unpack)
import GHC.IO.Encoding (setLocaleEncoding)
import MAlonzo.Code.VerifiedCompilation (runCertifierMain)
import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant)
import System.Exit
import System.FilePath
import System.IO
import System.Process
import Test.Tasty
import Test.Tasty.Extras (goldenVsTextM)
import Test.Tasty.HUnit
import Transform.Simplify
import Transform.Simplify.Lib
import UntypedPlutusCore

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
  (exitCode, result, _) <- readProcessWithExitCode "agda-with-stdlib-and-metatheory" [file] []
  return (exitCode, result)


agdaTestCert :: [ String ] -> String -> Assertion
agdaTestCert path name = do
    _ <- makeUplcCert path name
    makeAgdaLibFile
    (resCode, resText) <- runAgda "TestCert.agda"
    assertBool (name ++ " creates an invalid certificate:" ++ resText) (resCode == ExitSuccess)

makeAgdaLibFile :: Assertion
makeAgdaLibFile = do
    let name = "TestCert.agda-lib"
    let contents = unlines
          [ "depend:"
          , "  plutus-metatheory"
          , "  standard-library-2.1.1"
          , "include: ."
          , "  name: test-cert"
          ]
    writeFile name contents

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

type SimplifierFunc
  = Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> PLC.Quote
      ( Term Name PLC.DefaultUni PLC.DefaultFun ()
      , SimplifierTrace Name PLC.DefaultUni PLC.DefaultFun ()
      )

mkUPLCTest
  :: SimplifierFunc
  -> String
  -> Term Name DefaultUni DefaultFun ()
  -> TestTree
mkUPLCTest simplifierFunc name input = testCase name $
  let rawAgdaTrace = PLC.runQuote $ do
        simplifierTrace <- snd <$> simplifierFunc input
        return $ mkAgdaTrace simplifierTrace
  in
    case runCertifierMain rawAgdaTrace of
      Just result ->
        assertBool "The certifier returned false." result
      Nothing ->
        assertFailure "The certifier exited with an error."

mkMockTracePair
  :: SimplifierStage
  -> Term Name DefaultUni DefaultFun ()
  -> Term Name DefaultUni DefaultFun ()
  -> SimplifierTrace Name DefaultUni DefaultFun ()
mkMockTracePair stage before' after' =
  SimplifierTrace
    { simplifierTrace =
        [ Simplification
            { beforeAST = before'
            , stage = stage
            , afterAST = after'
            }
        ]
    }

runCertifierWithMockTrace
  :: SimplifierTrace Name DefaultUni DefaultFun ()
  -> IO Bool
runCertifierWithMockTrace trace = do
  let rawAgdaTrace = mkAgdaTrace trace
  case runCertifierMain rawAgdaTrace of
    Just result -> pure result
    Nothing ->
      assertFailure "The certifier exited with an error."

testTrivialSuccess1 :: TestTree
testTrivialSuccess1 =
  testCase "testTrivialSuccess1" $ do
    let before' = mkConstant () (1 :: Integer)
        after' = mkConstant () (1 :: Integer)
        trace = mkMockTracePair FloatDelay before' after'
    result <- runCertifierWithMockTrace trace
    assertBool "The certifier returned false." result

testTrivialFailure1 :: TestTree
testTrivialFailure1 =
  testCase "testTrivialFailure1" $ do
    let before' = mkConstant () (1 :: Integer)
        after' = mkConstant () (2 :: Integer)
        trace = mkMockTracePair FloatDelay before' after'
    result <- runCertifierWithMockTrace trace
    assertBool "The certifier returned true when it shouldn't have." (not result)

mkUPLCSimplifierTest
  :: String
  -> Term Name DefaultUni DefaultFun ()
  -> TestTree
mkUPLCSimplifierTest = mkUPLCTest testSimplify

mkUPLCCseTest
  :: String
  -> Term Name DefaultUni DefaultFun ()
  -> TestTree
mkUPLCCseTest = mkUPLCTest testCse

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
    , testGroup "uplc simplifier tests"
        $ fmap (uncurry mkUPLCSimplifierTest) testSimplifyInputs'
    , testGroup "uplc cse tests"
        $ fmap (uncurry mkUPLCCseTest) testCseInputs
    , testGroup "certifier unit tests"
        [ testTrivialSuccess1
        , testTrivialFailure1
        ]
    ]
  where
    -- TODO(https://github.com/IntersectMBO/plutus-private/issues/1541):
    --   this removes two tests which are currently failing; we should
    --   fix the tests and add them back
    testSimplifyInputs' =
      filter
        (\(name, _) ->
          name /= "forceDelaySimple" && name /= "forceDelayComplex"
        )
        testSimplifyInputs
