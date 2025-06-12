-- Copyright 2024 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Int.IntN(module Data.Int.IntN) where
import Prelude qualified ()
import Primitives

-- Just the types for sized Int.
-- The types are exported in Data.Int, instances are in Data.Int.Instances

newtype Int8 = I8 Int
unI8 :: Int8 -> Int
unI8 (I8 x) = x

newtype Int16 = I16 Int
unI16 :: Int16 -> Int
unI16 (I16 x) = x

newtype Int32 = I32 Int
unI32 :: Int32 -> Int
unI32 (I32 x) = x

newtype Int64 = I64 Int
unI64 :: Int64 -> Int
unI64 (I64 x) = x
