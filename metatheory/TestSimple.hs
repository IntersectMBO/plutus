{-# LANGUAGE PackageImports #-}

module Main where

import           Control.Exception
import           System.Environment
import           System.Exit
import           System.Process

import qualified MAlonzo.Code.Main  as M

succeedingEvalTests = ["succInteger"
--        ,"unitval"
--        ,"true"
--        ,"false"
        ,"churchZero"
        ,"churchSucc"
        ,"overapplication"
        ,"factorial"
        ,"fibonacci"
        ,"NatRoundTrip"
        ,"ListSum"
        ,"IfIntegers"
        ,"ApplyAdd1"
        ,"ApplyAdd2"
        ]

failingEvalTests = [] -- ["DivideByZero"]

succeedingTCTests = ["succInteger"
--        ,"unitval"
--        ,"true"
--        ,"false"
        ,"churchZero"
        ,"churchSucc"
--        ,"overapplication"
--        ,"factorial"
--        ,"fibonacci"
        ,"NatRoundTrip"
        ,"ListSum"
--        ,"IfIntegers"
--        ,"ApplyAdd1"
--        ,"ApplyAdd2"
        ]



-- this is likely to raise either an exitFailure or exitSuccess exception
runTest :: String -> String -> IO ()
runTest mode test = do
  example <- readProcess "plc" ["example","-s",test] []
  writeFile "tmp" example
  putStrLn $ "test: " ++ test ++ " [" ++ mode ++ "]"
  withArgs [mode,"--file","tmp"]  M.main

runSucceedingTests :: String -> [String] -> IO ()
runSucceedingTests mode [] = return ()
runSucceedingTests mode (test:tests) = catch
  (runTest mode test)
  (\ e -> case e of
      ExitFailure _ -> exitFailure
      ExitSuccess   -> runSucceedingTests mode tests)

runFailingTests :: String -> [String] -> IO ()
runFailingTests mode [] = return ()
runFailingTests mode (test:tests) = catch
  (runTest mode test)
  (\ e -> case e of
      ExitFailure _ -> runFailingTests mode tests
      ExitSuccess   -> exitSuccess)

main = do
  runSucceedingTests "evaluate" succeedingEvalTests
  runFailingTests "evaluate" failingEvalTests
--  runSucceedingTests "typecheck" succeedingTCTests

