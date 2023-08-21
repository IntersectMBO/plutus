module Main
where

import PlutusBenchmark.Ed25519.Common (runTests)
import System.IO (stdout)

main :: IO ()
main = runTests stdout
