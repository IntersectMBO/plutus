-- editorconfig-checker-disable-file
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE ViewPatterns #-}

#include "MachDeps.h"

{-|
Adapted from 'Data.SafeInt' to perform saturating arithmetic (i.e. returning max or min bounds) instead of throwing on overflow.

This is not quite as fast as using 'Int' or 'Int64' directly, but we need the safety. -}
module Data.SatInt
  ( -- Not exporting the constructor, so that 'coerce' doesn't work, see 'unsafeToSatInt'.
    SatInt (unSatInt)
  , unsafeToSatInt
  , fromSatInt
  , dividedBy
  ) where

import Codec.Serialise (Serialise)
import Control.DeepSeq (NFData)
import Data.Aeson (FromJSON, ToJSON)
import Data.Bits
import Data.Coerce
import Data.Csv
import Data.Int (Int64)
import Data.Primitive (Prim)
import GHC.Generics
import GHC.Natural
import Language.Haskell.TH.Syntax (Lift)
import NoThunks.Class

#if WORD_SIZE_IN_BITS >= 64
import GHC.Exts (addIntC#, andI#, int64ToInt#, intToInt64#, isTrue#, subIntC#, timesInt2#,
                 (<#), (<=#), (>#), (>=#))
import GHC.Int (Int64 (I64#))
import GHC.Real (overflowError)
#endif

newtype SatInt = SI {unSatInt :: Int64}
  deriving newtype (Show, Read, Eq, Ord, Bounded, NFData, Bits, FiniteBits, Prim)
  deriving stock (Lift, Generic)
  deriving (FromJSON, ToJSON) via Int64
  deriving (FromField) via Int64 -- For reading cost model data from CSV input
  deriving (Serialise) via Int64
  deriving anyclass (NoThunks)

{-| Wrap an 'Int' as a 'SatInt'. This is unsafe because the 'Int' can be a result of an arbitrary
potentially underflowing/overflowing operation. -}
unsafeToSatInt :: Int64 -> SatInt
unsafeToSatInt = SI
{-# INLINE unsafeToSatInt #-}

-- | An optimized version of @fromIntegral . unSatInt@.
fromSatInt :: forall a. Num a => SatInt -> a
fromSatInt = coerce (fromIntegral :: Int64 -> a)
{-# INLINE fromSatInt #-}

{-| In the `Num' instance, we plug in our own addition, multiplication
and subtraction function that perform overflow-checking. -}
instance Num SatInt where
  {-# INLINE (+) #-}
  (+) = plusSI

  {-# INLINE (*) #-}
  (*) = timesSI

  {-# INLINE (-) #-}
  (-) = minusSI

  {-# INLINE negate #-}
  negate (SI y)
    | y == minBound = maxBound
    | otherwise = SI (negate y)

  {-# INLINE abs #-}
  abs x
    | x >= 0 = x
    | otherwise = negate x

  {-# INLINE signum #-}
  signum = coerce (signum :: Int64 -> Int64)

  {-# INLINE fromInteger #-}
  fromInteger x
    | x > maxBoundInteger = maxBound
    | x < minBoundInteger = minBound
    | otherwise = SI (fromInteger x)

{-| Divide a `SatInt` by a natural number.  If the natural number is zero,
return `maxBound`; if we're at the maximum or minimum value then leave the
input unaltered. This should never throw. -}
dividedBy :: SatInt -> Natural -> SatInt
dividedBy _ 0 = maxBound
dividedBy x@(SI n) d =
  if n == maxBound || n == minBound
    then x
    else SI (n `div` (fromIntegral d))
{-# INLINE dividedBy #-}

maxBoundInteger :: Integer
maxBoundInteger = toInteger (maxBound :: Int64)
{-# INLINEABLE maxBoundInteger #-}

minBoundInteger :: Integer
minBoundInteger = toInteger (minBound :: Int64)
{-# INLINEABLE minBoundInteger #-}

{-
'addIntC#', 'subIntC#', and 'timesInt2#' have tricky returns:
all of them return non-zero (*not* necessarily 1) in the case of an overflow,
so we can't use 'isTrue#'; and the first two return a truncated value in
case of overflow, but this is *not* the same as the saturating result,
but rather a bitwise truncation that is typically not what we want.

So we have to case on the result, and then do some logic to work out what
kind of overflow we're facing, and pick the correct result accordingly.
-}

#if WORD_SIZE_IN_BITS >= 64

-- On 64-bit native targets, 'Int#' and 'Int64#' have the same machine
-- representation, so the int64ToInt#/intToInt64# casts are zero-cost. This
-- lets us use GHC's overflow-detecting primitives ('addIntC#', 'subIntC#',
-- 'timesInt2#'), which on x86_64/aarch64 lower to a small number of machine
-- instructions with an overflow-flag check.

plusSI :: SatInt -> SatInt -> SatInt
plusSI (SI (I64# a64#)) (SI (I64# b64#)) =
  case (# int64ToInt# a64#, int64ToInt# b64# #) of
    (# x#, y# #) ->
      case addIntC# x# y# of
        (# r#, 0# #) -> SI (I64# (intToInt64# r#))
        -- Overflow
        _ ->
          if isTrue# ((x# ># 0#) `andI#` (y# ># 0#))
            then maxBound
            else
              if isTrue# ((x# <# 0#) `andI#` (y# <# 0#))
                then minBound
                -- x and y have opposite signs, and yet we've overflowed,
                -- should be impossible
                else overflowError
{-# INLINE plusSI #-}

minusSI :: SatInt -> SatInt -> SatInt
minusSI (SI (I64# a64#)) (SI (I64# b64#)) =
  case (# int64ToInt# a64#, int64ToInt# b64# #) of
    (# x#, y# #) ->
      case subIntC# x# y# of
        (# r#, 0# #) -> SI (I64# (intToInt64# r#))
        -- Overflow
        _ ->
          if isTrue# ((x# >=# 0#) `andI#` (y# <# 0#))
            then maxBound
            else
              if isTrue# ((x# <=# 0#) `andI#` (y# ># 0#))
                then minBound
                -- x and y have the same sign, and yet we've overflowed,
                -- should be impossible
                else overflowError
{-# INLINE minusSI #-}

timesSI :: SatInt -> SatInt -> SatInt
timesSI (SI (I64# a64#)) (SI (I64# b64#)) =
  case (# int64ToInt# a64#, int64ToInt# b64# #) of
    (# x#, y# #) ->
      case timesInt2# x# y# of
        (# 0#, _, lo# #) -> SI (I64# (intToInt64# lo#))
        -- Overflow
        _ ->
          if isTrue# ((x# ># 0#) `andI#` (y# ># 0#))
            then maxBound
            else
              if isTrue# ((x# ># 0#) `andI#` (y# <# 0#))
                then minBound
                else
                  if isTrue# ((x# <# 0#) `andI#` (y# ># 0#))
                    then minBound
                    else
                      if isTrue# ((x# <# 0#) `andI#` (y# <# 0#))
                        then maxBound
                        -- Logically unreachable unless x or y is 0, in which
                        -- case it should be impossible to overflow
                        else overflowError
{-# INLINE timesSI #-}

#else

-- 32-bit targets (incl. wasm32). 'Int#' is too narrow to hold an 'Int64', so
-- we use a portable, boxed implementation. This is slower than the unboxed
-- path above, but correctness is preserved on platforms where the fast path
-- isn't representable.

plusSI :: SatInt -> SatInt -> SatInt
plusSI (SI a) (SI b) =
  let r = a + b
   in if a > 0 && b > 0 && r < 0
        then maxBound
        else
          if a < 0 && b < 0 && r >= 0
            then minBound
            else SI r
{-# INLINE plusSI #-}

minusSI :: SatInt -> SatInt -> SatInt
minusSI (SI a) (SI b) =
  let r = a - b
   in if a >= 0 && b < 0 && r < 0
        then maxBound
        else
          if a < 0 && b > 0 && r > 0
            then minBound
            else SI r
{-# INLINE minusSI #-}

timesSI :: SatInt -> SatInt -> SatInt
timesSI (SI a) (SI b) =
  let a' = toInteger a
      b' = toInteger b
      r = a' * b'
   in if r > maxBoundInteger
        then maxBound
        else
          if r < minBoundInteger
            then minBound
            else SI (fromInteger r)
{-# INLINE timesSI #-}

#endif

-- Specialized versions of several functions. They're specialized for
-- Int in the GHC base libraries. We try to get the same effect by
-- including specialized code and adding a rewrite rule.

sumSI :: [SatInt] -> SatInt
sumSI l = sum' l 0
  where
    sum' [] a = a
    sum' (x : xs) a = sum' xs $! a + x

productSI :: [SatInt] -> SatInt
productSI l = prod l 1
  where
    prod [] a = a
    prod (x : xs) a = prod xs $! a * x

{-# RULES
"sum/SatInt" sum = sumSI
"product/SatInt" product = productSI
  #-}
