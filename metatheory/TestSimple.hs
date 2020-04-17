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
        ,"ListSum"
        ,"IfIntegers"
        ,"ApplyAdd1"
        ,"ApplyAdd2"
        ]

untypedEvalTests = ["succInteger"
        ,"unitval"
        ,"true"
        ,"false"
        ,"churchZero"
        ,"churchSucc"
--        ,"overapplication"
--        ,"factorial"
--        ,"fibonacci"
        ,"NatRoundTrip"
        ,"ListSum"
--        ,"IfIntegers"
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
        ,"ListSum"
        ,"IfIntegers"
        ,"ApplyAdd1"
        ,"ApplyAdd2"
        ]

blah :: Maybe String -> [String]
blah Nothing = []
blah (Just mode) = ["--mode",mode]

-- this is likely to raise either an exitFailure or exitSuccess exception
runTest :: String -> Maybe String -> String -> IO ()
runTest command mode test = do
  example <- readProcess "plc" ["example","-s",test] []
  writeFile "tmp" example
  putStrLn $ "test: " ++ test ++ " [" ++ command ++ "]"
  withArgs ([command,"--file","tmp"] ++ blah mode)  M.main

runSucceedingTests :: String -> Maybe String -> [String] -> IO ()
runSucceedingTests command mode [] = return ()
runSucceedingTests command mode (test:tests) = catch
  (runTest command mode test)
  (\ e -> case e of
      ExitFailure _ -> exitFailure
      ExitSuccess   -> runSucceedingTests command mode tests)

runFailingTests :: String -> Maybe String -> [String] -> IO ()
runFailingTests command mode [] = return ()
runFailingTests command mode (test:tests) = catch
  (runTest command mode test)
  (\ e -> case e of
      ExitFailure _ -> runFailingTests command mode tests
      ExitSuccess   -> exitSuccess)

main = do
  putStrLn "running succ L..."
  runSucceedingTests "evaluate" (Just "L") succeedingEvalTests
  putStrLn "running fail L"
  runFailingTests "evaluate" (Just "L") failingEvalTests
  putStrLn "running succ CK"
  runSucceedingTests "evaluate" (Just "CK") succeedingEvalTests
  putStrLn "running fail CK"
  runFailingTests "evaluate" (Just "CK") failingEvalTests
  putStrLn "running succ U..."
  runSucceedingTests "evaluate" (Just "U") untypedEvalTests
  putStrLn "running succ TC"
  runSucceedingTests "typecheck" Nothing succeedingTCTests

