module Main where

import Common
import Criterion
import PlutusBenchmark.Common (unDeBruijnAnonTerm)
import PlutusCore qualified as PLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

{-|
for each data/*.flat validation script, it benchmarks
the whole time taken from script deserialization to script execution result.

 Run the benchmarks.  You can run groups of benchmarks by typing things like
     `stack bench -- plutus-benchmark:validation-full --ba crowdfunding`
   or
     `cabal bench -- plutus-benchmark:validation-full --benchmark-options crowdfunding`.
-}
main :: IO ()
main = benchWith mkFullBM
  where
    mkFullBM file scriptBS = whnf (UPLC.unsafeEvaluateCekNoEmit PLC.defaultCekParameters
                                  . unDeBruijnAnonTerm
                                  . unsafeUnflat file
                                  ) scriptBS

