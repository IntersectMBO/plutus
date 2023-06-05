module Main where

import PlutusBenchmark.BLS12_381.RunTests (runTests)
import System.IO (stdout)

main :: IO ()
main = runTests stdout
