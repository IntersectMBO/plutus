{- | Validation benchmarks for the Agda CEK machine. -}

{-# LANGUAGE BangPatterns #-}
module Main where

import PlutusBenchmark.Agda.Common (benchTermAgdaCek)
import PlutusBenchmark.Common (toNamedDeBruijnTerm)
import PlutusBenchmark.Validation.Common (benchWith, unsafeUnflat)
import UntypedPlutusCore qualified as UPLC

import Control.DeepSeq (force)

-- Run the validation benchmarks using the Agda CEK machine.
main :: IO ()
main = do
  let mkAgdaCekBM file program =
          let !benchTerm = force . toNamedDeBruijnTerm . UPLC._progTerm $ unsafeUnflat file program
          in benchTermAgdaCek benchTerm
  benchWith mkAgdaCekBM
