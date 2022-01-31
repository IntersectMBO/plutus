module Main where

import Common

-- | for each data/*.flat validation script, it benchmarks
-- the whole time taken from script deserialization to script execution result.
main :: IO ()
main = validationBench Full
