module Main where

import Types
import GetOpt
import Mode.HelpVersion
import Mode.PrintBuiltins
import Mode.ListExamples
import Mode.Compile
import Mode.Run
import Mode.Bench
import Mode.Debug

import System.Environment
import System.Exit

main :: IO ()
main = do
    opts <- GetOpt.parseArgs =<< getArgs
    let ?opts = opts
      in case _mode ?opts of
        Help{} -> runHelp
        Version{} -> runVersion
        PrintBuiltins{} -> runPrintBuiltins
        ListExamples{} -> runListExamples
        m -> do
            ast <- runCompile
            case m of
                Run{} -> runRun ast
                Bench{} -> runBench ast
                Debug{} -> runDebug ast
                Compile{} -> exitSuccess -- nothing left to do
