{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE PackageImports #-}

module Main where

import Control.Exception
import System.Environment
import System.Exit
import System.IO.Extra
import System.Process

import MAlonzo.Code.Main qualified as M

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

failingEvalTests = ["DivideByZero"]

type Mode = String
data Command = Evaluate Mode | Typecheck deriving Show

-- For each Command construct arguments to pass to plc-agda
mkArgs :: String -> Command -> [String]
mkArgs file (Evaluate mode) = ["evaluate","--input",file,"--mode",mode]
mkArgs file Typecheck       = ["typecheck","--input",file]

-- For each Command determine which executable should generate examples
exampleGenerator :: Command -> String
exampleGenerator (Evaluate "U") = "uplc"
exampleGenerator _              = "plc"

runTest :: Command -> String -> IO ()
runTest command test = withTempFile $ \tmp -> do
  example <- readProcess (exampleGenerator command) ["example", "-s",test] []
  writeFile tmp example
  putStrLn $ "test: " ++ test ++ " [" ++ show command ++ "]"
  withArgs (mkArgs tmp command) M.main

runSucceedingTests :: Command -> [String] -> IO ()
runSucceedingTests command [] = return ()
runSucceedingTests command (test:tests) = catch
  (runTest command test)
  (\case
    ExitFailure _ -> exitFailure
    ExitSuccess   -> runSucceedingTests command tests)

runFailingTests :: Command -> [String] -> IO ()
runFailingTests command [] = return ()
runFailingTests command (test:tests) = catch
  (runTest command test)
  (\case
    ExitFailure _ -> runFailingTests command tests
    ExitSuccess   -> exitFailure)

main = do
  -- Evaluation tests
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

  putStrLn "Typechecking succ"
  runSucceedingTests Typecheck succeedingEvalTests
