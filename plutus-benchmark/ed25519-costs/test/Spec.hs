module Main where

import PlutusBenchmark.Common (goldenVsTextualOutput)
import PlutusBenchmark.Ed25519.Common (runTests)

outputFile :: String
outputFile = "ed25519-costs.txt"

goldenFile :: FilePath
goldenFile = "ed25519-costs/test/ed25519-costs.golden"

main :: IO ()
main = goldenVsTextualOutput "Ed25519 costs test" goldenFile outputFile runTests
