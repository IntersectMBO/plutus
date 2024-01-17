{- | Validation benchmarks for the CEK machine. -}

{-# LANGUAGE BangPatterns #-}
module Main where

import Common (benchWith, evaluateCekLikeInProd, mkEvalCtx, unsafeUnflat)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import PlutusBenchmark.Common (toNamedDeBruijnTerm)
import UntypedPlutusCore as UPLC

import Criterion (whnf)

{-|
 Benchmarks only for the CEK execution time of the data/*.flat validation scripts

 Run the benchmarks.  You can run groups of benchmarks by typing things like
     `stack bench -- plutus-benchmark:validation --ba crowdfunding`
   or
     `cabal bench -- plutus-benchmark:validation --benchmark-options crowdfunding`.
-}
main :: IO ()
main = do
  evalCtx <- evaluate $ force mkEvalCtx
  let mkCekBM file program =
          -- don't count the undebruijn . unflat cost
          -- `force` to try to ensure that deserialiation is not included in benchmarking time.
          let !benchTerm = force . toNamedDeBruijnTerm . UPLC._progTerm $ unsafeUnflat file program
              eval = either (error . show) (\_ -> ()) . evaluateCekLikeInProd evalCtx
          in whnf eval benchTerm
  benchWith mkCekBM
