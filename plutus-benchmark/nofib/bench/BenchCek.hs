{-# LANGUAGE BangPatterns #-}

{- | Plutus benchmarks for the CEK machine based on some nofib examples. -}
module Main where

import Shared (benchWith, evaluateCekLikeInProd, mkEvalCtx)

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Criterion (whnf)

main :: IO ()
main = do
  evalCtx <- evaluate $ force mkEvalCtx
  let mkCekBM term =
          -- `force` to try to ensure that deserialiation is not included in benchmarking time.
          let !benchTerm = force term
              eval = either (error . show) (\_ -> ()) . evaluateCekLikeInProd evalCtx
          in whnf eval benchTerm
  benchWith mkCekBM
