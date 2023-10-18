module Main where

import PlutusBenchmark.BLS12_381.RunTests (runTests)
import PlutusBenchmark.Common (checkGoldenFileExists, goldenVsTextualOutput)

import Test.Tasty.Extras (makeVersionedFilePath)

outputFile :: FilePath
outputFile = "bls12-381-costs.txt"

goldenFile :: FilePath
goldenFile = makeVersionedFilePath ["bls12-381-costs", "test"] "bls12-381-costs.golden"

main :: IO ()
main = do
  checkGoldenFileExists goldenFile -- See Note [Paths to golden files]
  goldenVsTextualOutput "BLS12-381 costs test" goldenFile outputFile runTests
