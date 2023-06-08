module Main where

import PlutusBenchmark.Common (checkGoldenFileExists, goldenVsTextualOutput)
import PlutusBenchmark.Ed25519.Common (runTests)

outputFile :: String
outputFile = "ed25519-costs.txt"

goldenFile :: FilePath
goldenFile = "ed25519-costs/test/ed25519-costs.golden"

main :: IO ()
main = do
  checkGoldenFileExists goldenFile -- See Note [Paths to golden files]
  goldenVsTextualOutput "Ed25519 costs test" goldenFile outputFile runTests
