-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Integer(
  _integerToIntList,
  _intListToInteger,
  ) where

-- For the combinator file we need a portable way to store
-- the Integer type.  We use [Int], with digits in a small base.
integerListBase :: Integer
integerListBase = 32768

-- These two functions return an (opaque) representation of an
-- Integer as [Int].
-- This is used by the compiler to generate Integer literals.
-- First _integerToIntList is used in the compiler to get a list of
-- Int, and the generated code will have a call to _intListToInteger.
_integerToIntList :: Integer -> [Int]
_integerToIntList i = if i < 0 then (-1::Int) : f (-i) else f i
  where f 0 = []
        f i = fromInteger r : f q  where (q, r) = quotRem i integerListBase

_intListToInteger :: [Int] -> Integer
_intListToInteger ads@(x : ds) = if x == -1 then - f ds else f ads
  where f = foldr (\ d a -> a * integerListBase + toInteger d) 0

