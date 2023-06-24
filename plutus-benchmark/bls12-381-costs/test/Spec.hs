module Main where

import PlutusBenchmark.BLS12_381.RunTests (runTests)
import PlutusBenchmark.Common (checkGoldenFileExists, goldenVsTextualOutput)

outputFile :: String
outputFile = "bls12-381-costs.txt"

goldenFile :: FilePath
goldenFile = "bls12-381-costs/test/bls12-381-costs.golden"

main :: IO ()
main = do
  checkGoldenFileExists goldenFile -- See Note [Paths to golden files]
  goldenVsTextualOutput "BLS12-381 costs test" goldenFile outputFile runTests
