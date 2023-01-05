{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE PackageImports #-}

module Main where

import Control.Exception
import System.Environment
import System.Exit
import System.IO.Extra
import System.Process

import MAlonzo.Code.Main qualified as M

-- |List of tests that are expected to succeed
succeedingEvalTests = ["succInteger"
        ,"unitval"
        ,"true"
        ,"false"
        ,"churchZero"
        ,"churchSucc"
        ,"overapplication"
        ,"factorial"
        ,"fibonacci"
        ,"NatRoundTrip"
        ,"ScottListSum"
        ,"IfIntegers"
        ,"ApplyAdd1"
        ,"ApplyAdd2"
        ]

-- |List of tests that are expected to fail
failingEvalTests = ["DivideByZero"]

type Mode = String
data Command = Evaluate Mode | Typecheck deriving Show

-- |For each Command construct arguments to pass to plc-agda
mkArgs :: String -> Command -> [String]
mkArgs file (Evaluate mode) = ["evaluate","--input",file,"--mode",mode]
mkArgs file Typecheck       = ["typecheck","--input",file]

-- |For each Command determine which executable should generate examples
exampleGenerator :: Command -> String
exampleGenerator (Evaluate "U") = "uplc"
exampleGenerator _              = "plc"

-- |@runTest cmd tst@ generates a @tst@ example and runs it with the given @cmd@.
runTest :: Command -> String -> IO ()
runTest command test = withTempFile $ \tmp -> do
  example <- readProcess (exampleGenerator command) ["example", "-s",test] []
  writeFile tmp example
  putStrLn $ "test: " ++ test ++ " [" ++ show command ++ "]"
  withArgs (mkArgs tmp command) M.main

-- |Run a list of tests with a given command expecting them to succeed.
runSucceedingTests :: Command -> [String] -> IO ()
runSucceedingTests command [] = return ()
runSucceedingTests command (test:tests) = catch
  (runTest command test)
  (\case
    ExitFailure _ -> exitFailure
    ExitSuccess   -> runSucceedingTests command tests)

-- |Run a list of tests with a given command expecting them to fail.
runFailingTests :: Command -> [String] -> IO ()
runFailingTests command [] = return ()
runFailingTests command (test:tests) = catch
  (runTest command test)
  (\case
    ExitFailure _ -> runFailingTests command tests
    ExitSuccess   -> exitFailure)

main = do
  -- Run evaluation tests for each mode
  putStrLn "running succ TCK"
  runSucceedingTests (Evaluate "TCK") succeedingEvalTests
  putStrLn "running fail TCK"
  runFailingTests (Evaluate "TCK") failingEvalTests

  putStrLn "running succ TCEK"
  runSucceedingTests (Evaluate "TCEK") succeedingEvalTests
  putStrLn "running fail TCEK"
  runFailingTests (Evaluate "TCEK") failingEvalTests

  putStrLn "running succ U..."
  runSucceedingTests (Evaluate "U") succeedingEvalTests
  putStrLn "running fail U..."
  runFailingTests (Evaluate "U") failingEvalTests

  putStrLn "running succ TL"
  runSucceedingTests (Evaluate "TL") succeedingEvalTests
  putStrLn "running fail TL"
  runFailingTests (Evaluate "TL") failingEvalTests

  -- Typechecking tests
  -- NOTE: Evaluation tests beginning with T already run the typechecker.
  --       The following is more of a test that the typechecking command works.
  putStrLn "Typechecking succ"
  runSucceedingTests Typecheck succeedingEvalTests
