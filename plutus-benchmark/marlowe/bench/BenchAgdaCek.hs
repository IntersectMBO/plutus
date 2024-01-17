{- | Benchmarks for the Agda CEK machine based on some Marlowe examples. -}

module Main where

import PlutusBenchmark.Common (benchProgramAgdaCek)
import Shared (runBenchmarks)

main :: IO ()
main = runBenchmarks benchProgramAgdaCek
