module Timing.Terms (increment, choose) where

import PlutusTx.Builtins qualified as PlutusTx

increment :: Integer -> Integer
increment number = PlutusTx.addInteger number 1
{-# INLINEABLE increment #-}

choose :: Bool -> Integer -> Integer
choose condition number = if condition then number else PlutusTx.addInteger number 2
{-# INLINEABLE choose #-}
