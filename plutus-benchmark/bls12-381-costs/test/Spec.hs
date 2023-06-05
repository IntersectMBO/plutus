module Main where

import PlutusBenchmark.BLS12_381.RunTests (runTests)
import PlutusBenchmark.Common (goldenVsTextualOutput)

outputFile :: String
outputFile = "bls12-381-costs.txt"

goldenFile :: FilePath
goldenFile = "bls12-381-benchmarks/test/bls12-381-costs.golden"

main :: IO ()
main = goldenVsTextualOutput "BLS12-381 costs test" goldenFile outputFile runTests
