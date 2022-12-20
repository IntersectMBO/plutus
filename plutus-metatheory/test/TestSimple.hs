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

-- For each mode determine which executable should generate examples
modeExampleGenerator :: String -> String
modeExampleGenerator "U" = "uplc"
modeExampleGenerator _   = "plc"

runTest :: String -> String -> String -> IO ()
runTest command mode test = withTempFile $ \tmp -> do
  example <- readProcess (modeExampleGenerator mode) ["example", "-s",test] []
  writeFile tmp example
  putStrLn $ "test: " ++ test ++ " [" ++ command ++ "]"
  withArgs [command,"--input",tmp,"--mode",mode]  M.main

runSucceedingTests :: String -> String -> [String] -> IO ()
runSucceedingTests command mode [] = return ()
runSucceedingTests command mode (test:tests) = catch
  (runTest command mode test)
  (\case
    ExitFailure _ -> exitFailure
    ExitSuccess   -> runSucceedingTests command mode tests)

runFailingTests :: String -> String -> [String] -> IO ()
runFailingTests command mode [] = return ()
runFailingTests command mode (test:tests) = catch
  (runTest command mode test)
  (\case
    ExitFailure _ -> runFailingTests command mode tests
    ExitSuccess   -> exitFailure)

main = do
  putStrLn "running succ TCK"
  runSucceedingTests "evaluate" "TCK" succeedingEvalTests
  putStrLn "running fail TCK"
  runFailingTests "evaluate" "TCK" failingEvalTests
  putStrLn "running succ TCEK"
  runSucceedingTests "evaluate" "TCEK" succeedingEvalTests
  putStrLn "running fail TCEK"
  runFailingTests "evaluate" "TCEK" failingEvalTests
  putStrLn "running succ U..."
  runSucceedingTests "evaluate" "U" succeedingEvalTests
  putStrLn "running fail U..."
  runFailingTests "evaluate" "U" failingEvalTests
  putStrLn "running succ TL"
  runSucceedingTests "evaluate" "TL" succeedingEvalTests
  putStrLn "running fail TL"
  runFailingTests "evaluate" "TL" failingEvalTests

-- TODO: Testing of typecheck command
