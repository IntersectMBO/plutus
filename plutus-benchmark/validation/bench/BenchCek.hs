{- | Validation benchmarks for the CEK machine. -}
module Main where

import Common (benchTermCek, benchWith, mkEvalCtx, unsafeUnflat)
import Control.Exception (evaluate)
import PlutusBenchmark.Common (toNamedDeBruijnTerm)
import UntypedPlutusCore as UPLC

{-|
 Benchmarks only for the CEK execution time of the data/*.flat validation scripts

 Run the benchmarks.  You can run groups of benchmarks by typing things like
     `stack bench -- plutus-benchmark:validation --ba crowdfunding`
   or
     `cabal bench -- plutus-benchmark:validation --benchmark-options crowdfunding`.
-}
main :: IO ()
main = do
  evalCtx <- evaluate mkEvalCtx
  let mkCekBM file program =
          benchTermCek evalCtx . toNamedDeBruijnTerm . UPLC._progTerm $ unsafeUnflat file program
  benchWith mkCekBM
