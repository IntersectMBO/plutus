{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PackageImports #-}

{-| The tests in this file run the various Adga PLC and UPLC evaluators on the
    examples provided by `plc example` and `uplc example` and checks that the
    tests succeed or fail as expected. -}
module Main where

import Control.Exception
import System.Environment
import System.Exit
import System.IO.Extra
import System.Process

import MAlonzo.Code.Main qualified as M

-- | List of tests that are expected to succeed
succeedingEvalTests :: [String]
succeedingEvalTests =
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

-- | List of tests that are expected to fail
failingEvalTests :: [String]
failingEvalTests = ["DivideByZero"]

type Mode = String
data Command = Evaluate Mode | Typecheck deriving stock (Show)

-- | For each Command construct arguments to pass to plc-agda
mkArgs :: String -> Command -> [String]
mkArgs file (Evaluate mode) = ["evaluate", "--input", file, "--mode", mode]
mkArgs file Typecheck = ["typecheck", "--input", file]

-- | For each Command determine which executable should generate examples
exampleGenerator :: Command -> String
exampleGenerator (Evaluate "U") = "uplc"
exampleGenerator _ = "plc"

-- | @runTest cmd tst@ generates a @tst@ example and runs it with the given @cmd@.
runTest :: Command -> String -> IO ()
runTest command test = withTempFile $ \tmp -> do
  example <- readProcess (exampleGenerator command) ["example", "-s", test] []
  writeFile tmp example
  putStrLn $ "test: " ++ test ++ " [" ++ show command ++ "]"
  withArgs (mkArgs tmp command) M.main

-- | Run a list of tests with a given command expecting them to succeed.
runSucceedingTests :: Command -> [String] -> IO ()
runSucceedingTests _ [] = return ()
runSucceedingTests command (test : tests) =
  catch
    (runTest command test)
    ( \case
        ExitFailure _ -> exitFailure
        ExitSuccess -> runSucceedingTests command tests
    )

-- | Run a list of tests with a given command expecting them to fail.
runFailingTests :: Command -> [String] -> IO ()
runFailingTests _ [] = return ()
runFailingTests command (test : tests) =
  catch
    (runTest command test)
    ( \case
        ExitFailure _ -> runFailingTests command tests
        ExitSuccess -> exitFailure
    )

main :: IO ()
main = do
  -- Run evaluation tests for each mode
  putStrLn "running succeeding tests using TCK"
  runSucceedingTests (Evaluate "TCK") succeedingEvalTests
  putStrLn "running failing tests using TCK"
  runFailingTests (Evaluate "TCK") failingEvalTests

  putStrLn "running succeeding tests using TCEK"
  runSucceedingTests (Evaluate "TCEK") succeedingEvalTests
  putStrLn "running failing tests using TCEK"
  runFailingTests (Evaluate "TCEK") failingEvalTests

  putStrLn "running succeeding tests using U..."
  runSucceedingTests (Evaluate "U") succeedingEvalTests
  putStrLn "running failing tests using U..."
  runFailingTests (Evaluate "U") failingEvalTests

  putStrLn "running succeeding tests using TL"
  runSucceedingTests (Evaluate "TL") succeedingEvalTests
  putStrLn "running failing tests using TL"
  runFailingTests (Evaluate "TL") failingEvalTests

  -- Typechecking tests
  -- NOTE: Evaluation tests beginning with T already run the typechecker.
  --       The following is more of a test that the typechecking command works.
  putStrLn "Typechecking succeeding tests"
  runSucceedingTests Typecheck succeedingEvalTests
