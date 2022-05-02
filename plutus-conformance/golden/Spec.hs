-- | This suite is for easy addition of tests. When run with the `accept` test option (- -test-options=--accept),
-- output files will be added to all tests without output files.
-- You are advised to manually check that the output is correct.

{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where

import Data.ByteString.Lazy qualified as BS
import System.Directory
import System.Environment
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (findByExtension, goldenVsString)

main :: IO ()
main = defaultMain =<< goldenTests

goldenTests :: IO TestTree
goldenTests = do
    args <- getArgs
    case args of
      [ext,dir,action] -> do
          allInputFiles <- findByExtension [ext] dir
          -- only choose the ones without an output file, so as to not edit the ones already with outputs
          inputFiles <- sequenceA $
                [do
                    noOutput <- findFile [dir] (testIn <> ".expected")
                    case noOutput of
                        Just _  -> pure []
                        Nothing -> pure [testIn] | testIn <- allInputFiles]
          return $ testGroup "Golden tests for generating output files"
            [ goldenVsString
                inputFile -- test name
                (inputFile <> ".expected") -- golden file path
                (chooseAction action)
            | inputFile <- concat inputFiles
            ]
      _ -> error $
            "Please input the 3 arguments for running the golden tests: " <>
            "(1) file extension to be searched " <>
            "(2) directory to be searched " <>
            "(3) eval (for evaluation tests) or typecheck (for typechecking tests). "

chooseAction :: String -> IO BS.ByteString
chooseAction action
  | action == "eval" = -- action whose result is tested
                    evalAction
  | action == "typecheck" =
    error "typechecking has not been implemented yet. Only evaluation tests (eval) are supported"
  | otherwise =
    error "Unsupported tests. Please choose either eval (for evaluation tests) or typecheck (for typechecking tests)."


