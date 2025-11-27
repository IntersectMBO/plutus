-- | Plutus benchmarks for the Agda CEK machine based on some nofib examples.
module Main where

import PlutusBenchmark.Agda.Common (benchTermAgdaCek)
import Shared (benchWith)

main :: IO ()
main = benchWith benchTermAgdaCek
