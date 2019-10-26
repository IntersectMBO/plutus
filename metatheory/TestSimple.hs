{-# LANGUAGE PackageImports #-}

module Main where

import           Control.Exception
import           System.Environment
import           System.Exit
import           System.Process

import qualified MAlonzo.Code.Main  as M

succeedingTests = ["succInteger"
        ,"unitval"
        ,"true"
        ,"false"
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

failingTests = ["DivideByZero"]

-- this is likely to raise either an exitFailure or exitSuccess exception
runTest :: String -> IO ()
runTest test = do
  example <- readProcess "plc" ["example","-s",test] []
  writeFile "tmp" example
  putStrLn $ "test: " ++ test
  withArgs ["evaluate","--file","tmp"]  M.main

runSucceedingTests :: [String] -> IO ()
runSucceedingTests [] = return ()
runSucceedingTests (test:tests) = catch
  (runTest test)
  (\ e -> case e of
      ExitFailure _ -> exitFailure
      ExitSuccess   -> runSucceedingTests tests)

runFailingTests :: [String] -> IO ()
runFailingTests [] = return ()
runFailingTests (test:tests) = catch
  (runTest test)
  (\ e -> case e of
      ExitFailure _ -> runFailingTests tests
      ExitSuccess   -> exitSuccess)

main = do
  runSucceedingTests succeedingTests
  runFailingTests failingTests

