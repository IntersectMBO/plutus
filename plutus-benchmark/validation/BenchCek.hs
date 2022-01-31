module Main where

import Common

-- | benchmarks only for the CEK execution time of the data/*.flat validation scripts
main :: IO ()
main = validationBench CekOnly
