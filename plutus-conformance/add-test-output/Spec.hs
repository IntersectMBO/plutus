-- | This executable is for easy addition of tests. When run,
-- output files will be added to all tests that had no output files.
-- You are advised to manually check that the output is correct.

{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where

import Common
import Data.Text qualified as T
import PlutusCore.Error
import PlutusCore.Evaluation.Result (EvaluationResult (..))
import PlutusCore.Pretty
import PlutusCore.Quote (runQuoteT)
import System.Directory
import System.Environment
import Test.Tasty.Golden (findByExtension)
import Text.Megaparsec
import UntypedPlutusCore.Parser as UPLC

main :: IO ()
main = do
    args <- getArgs
    case args of
      [ext,dir,action] -> do
          allInputFiles <- findByExtension [ext] dir
          -- only choose the ones without an output file, so as to not edit the ones already with outputs
          inputFiles <- sequenceA $
                [do
                    hasOut <- doesFileExist (testIn <> ".expected")
                    if hasOut then pure [] else pure [testIn] | testIn <- allInputFiles]
          case action of
            "eval" -> do
              mapM_
                (\inputFile -> do
                  inputStr <- readFile inputFile
                  let parsed = runQuoteT $ UPLC.parse UPLC.program inputFile $ T.pack inputStr
                      outFilePath = inputFile <> ".expected"
                  case parsed of
                    Left (ParseErrorB peb) -> do
                      -- warn the user that the file failed to parse
                      putStrLn $ inputFile <> " failed to parse. Error written to " <> outFilePath
                      writeFile outFilePath (errorBundlePretty peb)
                    Right pro -> do
                      res <- evalUplcProg (stripePosProg pro)
                      case res of
                        EvaluationSuccess prog -> do
                          putStrLn $ inputFile <> " evaluated; result written to " <> outFilePath
                          writeFile outFilePath (render $ pretty prog)
                        EvaluationFailure      -> do
                          -- warn the user that the file failed to evaluate
                          putStrLn $ inputFile <> " failed to evaluate. Failure written to " <> outFilePath
                          writeFile outFilePath ((show :: EvaluationResult UplcProg -> String) EvaluationFailure)
                )
                (concat inputFiles)
            "typecheck" ->
              putStrLn "typechecking has not been implemented yet. Only evaluation tests (eval) are supported."
            _ -> error $
              "Unsupported test " <> show action <>
              ". Please choose either eval (for evaluation tests) or typecheck (for typechecking tests)."
      _ -> do
        mapM_
          putStrLn
          ["Please input the 3 arguments for running the golden tests: "
          , "(1) file extension to be searched "
          , "(2) directory to be searched "
          , "(3) eval (for evaluation tests) or typecheck (for typechecking tests). "
          , "E.g. run "
          , "`cabal run add-test-output \".uplc\" \"plutus-conformance/uplc/\" eval` "
          , "to have the executable search for files with extension `.uplc` in the /uplc directory that are missing output files. "
          , " It will evaluate and create output files for them."
          ]

