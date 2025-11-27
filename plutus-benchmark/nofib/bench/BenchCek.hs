{-# LANGUAGE BangPatterns #-}

-- | Plutus benchmarks for the CEK machine based on some nofib examples.
module Main where

import PlutusBenchmark.Common (mkMostRecentEvalCtx)
import Shared (benchTermCek, benchWith)

import Control.Exception (evaluate)

main :: IO ()
main = do
  evalCtx <- evaluate mkMostRecentEvalCtx
  benchWith $ benchTermCek evalCtx
