-- editorconfig-checker-disable-file
{- |
Adapted from 'Data.SafeInt' to perform saturating arithmetic (i.e. returning max or min bounds) instead of throwing on overflow.

This is not quite as fast as using 'Int' or 'Int64' directly, but we need the safety.
-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MagicHash      #-}
{-# LANGUAGE UnboxedTuples  #-}

module Data.SatInt
    ( -- Not exporting the constructor, so that 'coerce' doesn't work, see 'unsafeToSatInt'.
      SatInt (unSatInt)
    , unsafeToSatInt
    , fromSatInt
    ) where

import Codec.Serialise (Serialise)
import Control.DeepSeq (NFData)
import Data.Aeson (FromJSON, ToJSON)
import Data.Bits
import Data.Csv
import Data.Primitive (Prim)
import GHC.Base
import GHC.Generics
import GHC.Real
import Language.Haskell.TH.Syntax (Lift)
import NoThunks.Class

newtype SatInt = SI { unSatInt :: Int }
    deriving newtype (Show, Read, Eq, Ord, Bounded, NFData, Bits, FiniteBits, Prim)
    deriving stock (Lift, Generic)
    deriving (FromJSON, ToJSON) via Int
    deriving FromField via Int  -- For reading cost model data from CSV input
    deriving Serialise via Int
    deriving anyclass NoThunks

{-# INLINE unsafeToSatInt #-}
-- | Wrap an 'Int' as a 'SatInt'. This is unsafe because the 'Int' can be a result of an arbitrary
-- potentially underflowing/overflowing operation.
unsafeToSatInt :: Int -> SatInt
unsafeToSatInt = SI

{-# INLINE fromSatInt #-}
-- | An optimized version of @fromIntegral . unSatInt@.
fromSatInt :: forall a. Num a => SatInt -> a
fromSatInt = coerce (fromIntegral :: Int -> a)

-- | In the `Num' instance, we plug in our own addition, multiplication
-- and subtraction function that perform overflow-checking.
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
    | otherwise     = SI (negate y)

  {-# INLINE abs #-}
  abs x
    | x >= 0    = x
    | otherwise = negate x

  {-# INLINE signum #-}
  signum = coerce (signum :: Int -> Int)

  {-# INLINE fromInteger #-}
  fromInteger x
    | x > maxBoundInteger  = maxBound
    | x < minBoundInteger  = minBound
    | otherwise            = SI (fromInteger x)

{-# INLINABLE maxBoundInteger #-}
maxBoundInteger :: Integer
maxBoundInteger = toInteger maxInt

{-# INLINABLE minBoundInteger #-}
minBoundInteger :: Integer
minBoundInteger = toInteger minInt

{-
'addIntC#', 'subIntC#', and 'mulIntMayOflow#' have tricky returns:
all of them return non-zero (*not* necessarily 1) in the case of an overflow,
so we can't use 'isTrue#'; and the first two return a truncated value in
case of overflow, but this is *not* the same as the saturating result,
but rather a bitwise truncation that is typically not what we want.

So we have to case on the result, and then do some logic to work out what
kind of overflow we're facing, and pick the correct result accordingly.
-}

{-# INLINE plusSI #-}
plusSI :: SatInt -> SatInt -> SatInt
plusSI (SI (I# x#)) (SI (I# y#)) =
  case addIntC# x# y#  of
    (# r#, 0# #) -> SI (I# r#)
    -- Overflow
    _ ->
      if      isTrue# ((x# ># 0#) `andI#` (y# ># 0#)) then maxBound
      else if isTrue# ((x# <# 0#) `andI#` (y# <# 0#)) then minBound
      -- x and y have opposite signs, and yet we've overflowed, should
      -- be impossible
      else overflowError

{-# INLINE minusSI #-}
minusSI :: SatInt -> SatInt -> SatInt
minusSI (SI (I# x#)) (SI (I# y#)) =
  case subIntC# x# y# of
    (# r#, 0# #) -> SI (I# r#)
    -- Overflow
    _ ->
      if      isTrue# ((x# >=# 0#) `andI#` (y# <# 0#)) then maxBound
      else if isTrue# ((x# <=# 0#) `andI#` (y# ># 0#)) then minBound
      -- x and y have the same sign, and yet we've overflowed, should
      -- be impossible
      else overflowError

{-# INLINE timesSI #-}
timesSI :: SatInt -> SatInt -> SatInt
timesSI (SI (I# x#)) (SI (I# y#)) =
  case mulIntMayOflo# x# y# of
      0# -> SI (I# (x# *# y#))
      -- Overflow
      _ ->
          if      isTrue# ((x# ># 0#) `andI#` (y# ># 0#)) then maxBound
          else if isTrue# ((x# ># 0#) `andI#` (y# <# 0#)) then minBound
          else if isTrue# ((x# <# 0#) `andI#` (y# ># 0#)) then minBound
          else if isTrue# ((x# <# 0#) `andI#` (y# <# 0#)) then maxBound
          -- Logically unreachable unless x or y is 0, in which case
          -- it should be impossible to overflow
          else overflowError

-- Specialized versions of several functions. They're specialized for
-- Int in the GHC base libraries. We try to get the same effect by
-- including specialized code and adding a rewrite rule.

sumSI :: [SatInt] -> SatInt
sumSI     l       = sum' l 0
  where
    sum' []     a = a
    sum' (x:xs) a = sum' xs $! a + x

productSI :: [SatInt] -> SatInt
productSI l       = prod l 1
  where
    prod []     a = a
    prod (x:xs) a = prod xs $! a * x

{-# RULES
  "sum/SatInt"          sum = sumSI;
  "product/SatInt"      product = productSI
  #-}
