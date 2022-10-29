-- editorconfig-checker-disable-file
{- |
Adapted from 'Data.SafeInt' to perform saturating arithmetic (i.e. returning max or min bounds) instead of throwing on overflow.

This is not quite as fast as using 'Int' or 'Int64' directly, but we need the safety.
-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE CPP                #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE MagicHash          #-}
{-# LANGUAGE UnboxedTuples      #-}

-- This fires on GHC-9.2.4, may indicate a real problem,
-- but putting it off for now.
{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}
module Data.SatInt (SatInt) where

import Codec.Serialise (Serialise)
import Control.DeepSeq (NFData)
import Data.Aeson (FromJSON, ToJSON)
import Data.Bits
import Data.Csv
import Data.Primitive (Prim)
import GHC.Base
import GHC.Generics
#if MIN_VERSION_base(4,16,0)
import GHC.Integer (smallInteger)
#else
import GHC.Num (smallInteger)
#endif
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

instance Enum SatInt where
  {-# INLINE succ #-}
  succ = coerce (succ :: Int -> Int)

  {-# INLINE pred #-}
  pred = coerce (pred :: Int -> Int)

  {-# INLINE toEnum #-}
  toEnum = SI

  {-# INLINE fromEnum #-}
  fromEnum = unSatInt

  {-# INLINE enumFrom #-}
  enumFrom (SI (I# x)) = eftInt x maxInt#
      where !(I# maxInt#) = maxInt

  {-# INLINE enumFromTo #-}
  enumFromTo (SI (I# x)) (SI (I# y)) = eftInt x y

  {-# INLINE enumFromThen #-}
  enumFromThen (SI (I# x1)) (SI (I# x2)) = efdInt x1 x2

  {-# INLINE enumFromThenTo #-}
  enumFromThenTo (SI (I# x1)) (SI (I# x2)) (SI (I# y)) = efdtInt x1 x2 y

-- The following code is copied/adapted from GHC.Enum.

{-# RULES
"eftInt"        [~1] forall x y. eftInt x y = build (\ c n -> eftIntFB c n x y)
"eftIntList"    [1] eftIntFB  (:) [] = eftInt
 #-}

{-# NOINLINE [1] eftInt #-}
eftInt :: Int# -> Int# -> [SatInt]
-- [x1..x2]
eftInt x0 y | isTrue# (x0 ># y) = []
            | otherwise = go x0
               where
                 go x = SI (I# x) : if isTrue# (x ==# y) then [] else go (x +# 1#)

{-# INLINE [0] eftIntFB #-}
eftIntFB :: (SatInt -> r -> r) -> r -> Int# -> Int# -> r
eftIntFB c n x0 y | isTrue# (x0 ># y) = n
                  | otherwise = go x0
                 where
                   go x = SI (I# x) `c` if isTrue# (x ==# y) then n else go (x +# 1#)
                        -- Watch out for y=maxBound; hence ==, not >
        -- Be very careful not to have more than one "c"
        -- so that when eftInfFB is inlined we can inline
        -- whatever is bound to "c"

{-# RULES
"efdtInt"       [~1] forall x1 x2 y.
                     efdtInt x1 x2 y = build (\ c n -> efdtIntFB c n x1 x2 y)
"efdtIntUpList" [1]  efdtIntFB (:) [] = efdtInt
 #-}

efdInt :: Int# -> Int# -> [SatInt]
-- [x1,x2..maxInt]
efdInt x1 x2
 | isTrue# (x2 >=# x1) = case maxInt of I# y -> efdtIntUp x1 x2 y
 | otherwise = case minInt of I# y -> efdtIntDn x1 x2 y

{-# NOINLINE [1] efdtInt #-}
efdtInt :: Int# -> Int# -> Int# -> [SatInt]
-- [x1,x2..y]
efdtInt x1 x2 y
 | isTrue# (x2 >=# x1) = efdtIntUp x1 x2 y
 | otherwise = efdtIntDn x1 x2 y

{-# INLINE [0] efdtIntFB #-}
efdtIntFB :: (SatInt -> r -> r) -> r -> Int# -> Int# -> Int# -> r
efdtIntFB c n x1 x2 y
 | isTrue# (x2 >=# x1) = efdtIntUpFB c n x1 x2 y
 | otherwise  = efdtIntDnFB c n x1 x2 y

-- Requires x2 >= x1
efdtIntUp :: Int# -> Int# -> Int# -> [SatInt]
efdtIntUp x1 x2 y    -- Be careful about overflow!
 | isTrue# (y <# x2) = if isTrue# (y <# x1) then [] else [SI (I# x1)]
 | otherwise = -- Common case: x1 <= x2 <= y
               let !delta = x2 -# x1 -- >= 0
                   !y' = y -# delta  -- x1 <= y' <= y; hence y' is representable

                   -- Invariant: x <= y
                   -- Note that: z <= y' => z + delta won't overflow
                   -- so we are guaranteed not to overflow if/when we recurse
                   go_up x | isTrue# (x ># y') = [SI (I# x)]
                           | otherwise = SI (I# x) : go_up (x +# delta)
               in SI (I# x1) : go_up x2

-- Requires x2 >= x1
{-# INLINE [0] efdtIntUpFB #-}
efdtIntUpFB :: (SatInt -> r -> r) -> r -> Int# -> Int# -> Int# -> r
efdtIntUpFB c n x1 x2 y    -- Be careful about overflow!
 | isTrue# (y <# x2) = if isTrue# (y <# x1) then n else SI (I# x1) `c` n
 | otherwise = -- Common case: x1 <= x2 <= y
               let !delta = x2 -# x1 -- >= 0
                   !y' = y -# delta  -- x1 <= y' <= y; hence y' is representable

                   -- Invariant: x <= y
                   -- Note that: z <= y' => z + delta won't overflow
                   -- so we are guaranteed not to overflow if/when we recurse
                   go_up x | isTrue# (x ># y') = SI (I# x) `c` n
                           | otherwise = SI (I# x) `c` go_up (x +# delta)
               in SI (I# x1) `c` go_up x2

-- Requires x2 <= x1
efdtIntDn :: Int# -> Int# -> Int# -> [SatInt]
efdtIntDn x1 x2 y    -- Be careful about underflow!
 | isTrue# (y ># x2) = if isTrue# (y ># x1) then [] else [SI (I# x1)]
 | otherwise = -- Common case: x1 >= x2 >= y
               let !delta = x2 -# x1 -- <= 0
                   !y' = y -# delta  -- y <= y' <= x1; hence y' is representable

                   -- Invariant: x >= y
                   -- Note that: z >= y' => z + delta won't underflow
                   -- so we are guaranteed not to underflow if/when we recurse
                   go_dn x | isTrue# (x <# y') = [SI (I# x)]
                           | otherwise = SI (I# x) : go_dn (x +# delta)
   in SI (I# x1) : go_dn x2


-- Requires x2 <= x1
{-# INLINE [0] efdtIntDnFB #-}
efdtIntDnFB :: (SatInt -> r -> r) -> r -> Int# -> Int# -> Int# -> r
efdtIntDnFB c n x1 x2 y    -- Be careful about underflow!
 | isTrue# (y ># x2) = if isTrue# (y ># x1) then n else SI (I# x1) `c` n
 | otherwise = -- Common case: x1 >= x2 >= y
               let !delta = x2 -# x1 -- <= 0
                   !y' = y -# delta  -- y <= y' <= x1; hence y' is representable

                   -- Invariant: x >= y
                   -- Note that: z >= y' => z + delta won't underflow
                   -- so we are guaranteed not to underflow if/when we recurse
                   go_dn x | isTrue# (x <# y') = SI (I# x) `c` n
                           | otherwise = SI (I# x) `c` go_dn (x +# delta)
               in SI (I# x1) `c` go_dn x2

-- The following code is copied/adapted from GHC.Real.

instance Real SatInt where
  {-# INLINE toRational #-}
  toRational (SI x) = toInteger x % 1

instance Integral SatInt where
    {-# INLINE toInteger #-}
    toInteger (SI (I# i)) = smallInteger i

    {-# INLINE quot #-}
    SI a `quot` SI b
     | b == 0                     = divZeroError
     -- a/-1 = -a, -minBound = maxBound
     -- We can't just fall though since `quotInt` would overflow instead
     | a == minBound && b == (-1) = maxBound
     | otherwise                  = SI (a `quotInt` b)

    {-# INLINE rem #-}
    SI a `rem` SI b
     | b == 0                     = divZeroError
     -- a/-1 = -a, with no remainder
     -- We can't just fall though since `remInt` would overflow instead
     | a == minBound && b == (-1) = 0
     | otherwise                  = SI (a `remInt` b)

    {-# INLINE div #-}
    SI a `div` SI b
     | b == 0                     = divZeroError
     -- a/-1 = -a, -minBound = maxBound
     -- We can't just fall though since `divInt` would overflow instead
     | a == minBound && b == (-1) = maxBound
     | otherwise                  = SI (a `divInt` b)

    {-# INLINE mod #-}
    SI a `mod` SI b
     | b == 0                     = divZeroError
     -- a/-1 = -a, with no remainder
     -- We can't just fall though since `modInt` would overflow instead
     | a == minBound && b == (-1) = 0
     | otherwise                  = SI (a `modInt` b)

    {-# INLINE quotRem #-}
    SI a `quotRem` SI b
     | b == 0                     = divZeroError
     -- See cases for `quot` and `rem`
     | a == minBound && b == (-1) = (maxBound, 0)
     | otherwise                  =  a `quotRemSI` b

    {-# INLINE divMod #-}
    SI a `divMod` SI b
     | b == 0                     = divZeroError
     -- See cases for `div` and `mod`
     | a == minBound && b == (-1) = (maxBound, 0)
     | otherwise                  =  a `divModSI` b

{-# INLINE quotRemSI #-}
quotRemSI :: Int -> Int -> (SatInt, SatInt)
quotRemSI a@(I# _) b@(I# _) = (SI (a `quotInt` b), SI (a `remInt` b))

{-# INLINE divModSI #-}
divModSI ::  Int -> Int -> (SatInt, SatInt)
divModSI x@(I# _) y@(I# _) = (SI (x `divInt` y), SI (x `modInt` y))

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

{-# RULES
"fromIntegral/Int->SatInt"     fromIntegral = SI
"fromIntegral/SatInt->SatInt" fromIntegral = id :: SatInt -> SatInt
  #-}

-- Specialized versions of several functions. They're specialized for
-- Int in the GHC base libraries. We try to get the same effect by
-- including specialized code and adding a rewrite rule.

sumSI :: [SatInt] -> SatInt
sumSI     l       = sum' l 0
  where
    sum' []     a = a
    sum' (x:xs) a = sum' xs (a + x)

productSI :: [SatInt] -> SatInt
productSI l       = prod l 1
  where
    prod []     a = a
    prod (x:xs) a = prod xs (a*x)

{-# RULES
  "sum/SatInt"          sum = sumSI;
  "product/SatInt"      product = productSI
  #-}
