{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE PackageImports #-}

module Main where

import           Control.Exception
import           System.Environment
import           System.Exit
import           System.Process

import qualified MAlonzo.Code.Main  as M

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

succeedingTCTests = ["succInteger"
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

-- blah :: String -> [String]
-- blah "plc"     = []
-- blah mode = ["--mode",mode]

runTest :: String -> String -> String -> IO ()
runTest command mode test = do
  example <- readProcess mode ["example", "-s",test] []
  writeFile "tmp" example
  putStrLn $ "test: " ++ test ++ " [" ++ command ++ "]"
  withArgs [command,"--file","tmp"]  M.main

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
    ExitSuccess   -> exitSuccess)

main = do
{-
putStrLn "running succ L..."
  runSucceedingTests "evaluate" (Just "L") succeedingEvalTests
  putStrLn "running fail L"
  runFailingTests "evaluate" (Just "L") failingEvalTests
  putStrLn "running succ CK"
  runSucceedingTests "evaluate" (Just "CK") succeedingEvalTests
  putStrLn "running fail CK"
  runFailingTests "evaluate" (Just "CK") failingEvalTests
-}
  putStrLn "running succ TCK"
  runSucceedingTests "evaluate" "plc" succeedingEvalTests
  putStrLn "running fail TCK"
  runFailingTests "evaluate" "plc" failingEvalTests
  putStrLn "running succ TCEK"
  runSucceedingTests "evaluate" "plc" succeedingEvalTests
  putStrLn "running fail TCEK"
  runFailingTests "evaluate" "plc" failingEvalTests
  -- putStrLn "running succ U..."
  -- runSucceedingTests "evaluate" "uplc" succeedingEvalTests
  putStrLn "running fail U..."
  runFailingTests "evaluate" "uplc" failingEvalTests
  putStrLn "running succ TC"
  runSucceedingTests "typecheck" "plc" succeedingTCTests
