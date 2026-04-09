{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}

-- | Verifies that INLINEABLE pragma doesn't need to be written.
module Inlineable.Lib where

import PlutusTx.Prelude

fibonacci :: Integer -> Integer
fibonacci n
  | n < 0 = traceError "fibonacci: negative input"
  | n == 0 = 0
  | n == 1 = 1
  | otherwise = fibonacci (n - 1) + fibonacci (n - 2)

factorial :: Integer -> Integer
factorial n
  | n < 0 = traceError "factorial: negative input"
  | n == 0 = 1
  | otherwise = n * factorial (n - 1)

total :: Integer -> Integer
total n
  | n < 0 = traceError "total: negative input"
  | n == 0 = 0
  | otherwise = n + total (n - 1)

triple :: Integer -> (Integer, Integer, Integer)
triple n
  | n < 0 = traceError "triple: negative input"
  | otherwise = (fib, fac, tot)
  where
    fib = fibonacci n
    fac = factorial n
    tot = total n
