{-# LANGUAGE BangPatterns #-}
module Main where

import Common (benchWith, unsafeUnflat)
import PlutusBenchmark.Common (benchTermAgdaCek, toNamedDeBruijnTerm)
import UntypedPlutusCore qualified as UPLC

import Control.DeepSeq (force)

-- Run the validation benchmarks using the Agda CEK machine.
main :: IO ()
main = do
  let mkAgdaCekBM file program =
          let !benchTerm = force . toNamedDeBruijnTerm . UPLC._progTerm $ unsafeUnflat file program
          in benchTermAgdaCek benchTerm
  benchWith mkAgdaCekBM
