module Main where

import Common
import Criterion

{-|
for each data/*.flat validation script, it benchmarks
the time taken to only flat-deserialize the script

 Run the benchmarks.  You can run groups of benchmarks by typing things like
     `stack bench -- plutus-benchmark:validation-decode --ba crowdfunding`
   or
     `cabal bench -- plutus-benchmark:validation-decode --benchmark-options crowdfunding`.
-}
main :: IO ()
main = benchWith mkDecBM
  where
    mkDecBM file scriptBS = nf (unsafeUnflat file) scriptBS

