{- | Validation benchmarks for the Agda CEK machine. -}

{-# LANGUAGE BangPatterns #-}
module Main where

import Common (benchWith)
import PlutusBenchmark.Agda.Common (benchTermAgdaCek)

-- Run the validation benchmarks using the Agda CEK machine.
main :: IO ()
main = benchWith $ \(~_) (~_) -> benchTermAgdaCek
