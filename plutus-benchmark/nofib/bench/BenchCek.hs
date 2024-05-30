{-# LANGUAGE BangPatterns #-}

{- | Plutus benchmarks for the CEK machine based on some nofib examples. -}
module Main where

import Shared (benchTermCek, benchWith, mkEvalCtx)

import Control.Exception (evaluate)

main :: IO ()
main = do
  evalCtx <- evaluate mkEvalCtx
  benchWith $ benchTermCek evalCtx
