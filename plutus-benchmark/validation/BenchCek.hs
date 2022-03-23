{-# LANGUAGE BangPatterns #-}
module Main where

import Common
import Control.DeepSeq (force)
import Criterion
import PlutusBenchmark.Common
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Transform.Globalify
import Debug.Trace
{-|
 Benchmarks only for the CEK execution time of the data/*.flat validation scripts

 Run the benchmarks.  You can run groups of benchmarks by typing things like
     `stack bench -- plutus-benchmark:validation --ba crowdfunding`
   or
     `cabal bench -- plutus-benchmark:validation --benchmark-options crowdfunding`.
-}
main :: IO ()
main = benchWith mkCekBM
 where
   mkCekBM file program =
       let t = UPLC._progTerm $ unsafeUnflat file program
           (gt,maxTop) = globalifyTerm t
           !nterm = force (toNamedDeBruijnTerm gt)
       in traceShow (file,maxTop) $ whnf unsafeEvaluateCekNoEmit' nterm

