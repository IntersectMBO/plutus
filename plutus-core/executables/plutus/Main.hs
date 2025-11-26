{-# LANGUAGE ImplicitParams #-}

module Main where

import GetOpt
import Mode.Compile
import Mode.HelpVersion
import Mode.ListExamples
import Mode.PrintBuiltins
import Mode.PrintCostModel
import Types

import System.Environment

main :: IO ()
main = do
  opts <- GetOpt.parseArgs =<< getArgs
  let ?opts = opts
   in case _mode ?opts of
        Help {} -> runHelp
        Version {} -> runVersion
        PrintBuiltins {} -> runPrintBuiltins
        PrintCostModel {} -> runPrintCostModel
        ListExamples {} -> runListExamples
        Compile afterCompile -> runCompile afterCompile
